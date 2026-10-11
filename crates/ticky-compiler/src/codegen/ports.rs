//! The program's edges: input ports (with controls), output ports (incl. `--outputs=west`
//! gates and the `--checks` error output) and screens/speakers/panels.

use std::collections::HashMap;

use ticky_factorio::*;
use ticky_syntax::ast::PortDir;
use ticky_syntax::Diag;

use super::*;
use crate::program::Program;

/// Input ports: where each one's raw value is (by port index), and the controls.
#[allow(clippy::type_complexity)]
pub(super) fn input_ports(cg: &mut Cg, p: &Program, port_ents: &mut [EntId]) -> Result<(HashMap<usize, Ref>, Vec<(usize, EntId)>), Diag> {
    let t = SignalTable::base();
    let mut controls = Vec::new();
    let mut input_raw: HashMap<usize, Ref> = HashMap::new();
    for (pi, port) in p.ports.iter().enumerate() {
        if port.dir != PortDir::Input {
            continue;
        }
        let bundle = port.ty.is_bun();
        let (kind, raw) = if bundle {
            // Copies everything on the player's wires onto the program's own bundle wire.
            (arith(Operand::Sig(cg.each), ArOp::Add, Operand::Const(0), cg.each), Ref::Bun(cg.bnew()))
        } else {
            let raw = cg.alloc()?;
            (arith(Operand::Sig(port.sig), ArOp::Add, Operand::Const(0), raw), Ref::Op(Operand::Sig(raw)))
        };
        input_raw.insert(pi, raw);
        let id = cg.net.add(kind, Role::InputPort { name: port.name.clone(), signal: port.sig });
        let reads = if bundle { "every signal".to_string() } else { t.name(port.sig).to_string() };
        let e = &mut cg.net.entities[id];
        e.dir = Dir::East;
        e.description = Some(format!(
            "Ticky input `{}` ({}){}: reads {reads} from wires connected to this combinator's input (left) side.",
            port.name,
            port.ty.name(),
            port.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default(),
        ));
        match raw {
            Ref::Bun(b) => cg.bprod(b, id),
            _ => cg.nets[0].members.push((id, Conn::OutGreen)),
        }
        port_ents[pi] = id;
        // A control: a constant combinator beside the port, wired to its input.
        if let Some(ctl) = p.controls.iter().find(|c| c.name == port.name) {
            let (value, on) = if ctl.switch { (1, ctl.initial != 0) } else { (ctl.initial, true) };
            let k = cg.net.add(Kind::Constant(ConstComb { values: vec![(port.sig, value)], on }), Role::Control { port: id });
            let label = port.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default();
            cg.net.entities[k].description = Some(if ctl.switch {
                format!("Ticky control `{}`{label}: turn this constant combinator on or off.", port.name)
            } else {
                format!("Ticky control `{}`{label}: set the value of {} here.", port.name, t.name(port.sig))
            });
            // A network rather than a wire: relays carry it if the control is placed far away.
            cg.nets.push(NetSpec { red: true, members: vec![(k, Conn::Red), (id, Conn::InRed)] });
            controls.push((pi, k));
        }
    }
    Ok((input_raw, controls))
}

/// Output ports. `comb_ref`: where combinational outputs are read from.
pub(super) fn output_ports(cg: &mut Cg, p: &Program, shared: &Shared, comb_ref: &HashMap<usize, Ref>, port_ents: &mut [EntId], outputs_west: bool) {
    let t = SignalTable::base();
    let run = cg.run;
    // Output ports: the state's value while running, 0 when stopped.
    for (pi, port) in p.ports.iter().enumerate() {
        if port.dir != PortDir::Output {
            continue;
        }
        if p.error_port == Some(pi) {
            let e = cg.err.unwrap();
            let id = cg.net.add(arith(Operand::Sig(e), ArOp::Mul, Operand::Sig(run), port.sig), Role::OutputPort { name: port.name.clone(), signal: port.sig });
            if outputs_west {
                // Same shape as the other outputs: a gate here, the port at the west edge.
                cg.net.entities[id].role = Role::OutputGate { name: port.name.clone() };
            }
            cg.net.entities[id].dir = Dir::East;
            cg.net.entities[id].description = Some("Ticky output `error` (--checks): the code of the first failed runtime check (see the build report), 0 while all is well.".into());
            cg.nets[0].members.push((id, Conn::InGreen));
            port_ents[pi] = id;
            if outputs_west {
                let a = Arith { first: Operand::Sig(port.sig), first_nets: Nets::RED, second: Operand::Const(0), second_nets: Nets::BOTH, op: ArOp::Add, out: port.sig };
                let out = cg.net.add(Kind::Arith(a), Role::OutputPort { name: port.name.clone(), signal: port.sig });
                cg.net.entities[out].dir = Dir::West;
                port_ents[pi] = out;
            }
            continue;
        }
        let si = p.output_state(pi).unwrap();
        let s = &p.states[si];
        let each = cg.each;
        // Bundles: everything on the state's wire while running. Constant bundles: a
        // decider outputting the constants while running.
        let direct = comb_ref.get(&si).copied();
        let (kind, reads) = match (s.ty.is_bun(), direct.or(shared.state_sig.get(&si).map(|x| Ref::Op(Operand::Sig(*x)))), shared.state_bun.get(&si)) {
            (true, Some(Ref::Bun(x)), _) => {
                let a = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Sig(run), second_nets: Nets::GREEN, op: ArOp::Mul, out: each };
                (Kind::Arith(a), Some(x))
            }
            (false, Some(Ref::Op(Operand::Const(k))), _) => (arith(Operand::Sig(run), ArOp::Mul, Operand::Const(k), port.sig), None),
            (true, _, Some(&x)) => {
                let a = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Sig(run), second_nets: Nets::GREEN, op: ArOp::Mul, out: each };
                (Kind::Arith(a), Some(x))
            }
            (true, _, None) => {
                let outs = s.binit.iter().map(|(sg, k)| out_const(*sg, *k)).collect();
                (dec(vec![green(c(run, CmpOp::Ne, 0))], outs), None)
            }
            (false, Some(Ref::Op(Operand::Sig(x))), _) => (arith(Operand::Sig(x), ArOp::Mul, Operand::Sig(run), port.sig), None),
            (_, Some(_), _) => unreachable!("output of the wrong kind"),
            (false, None, _) => (arith(Operand::Sig(run), ArOp::Mul, Operand::Const(s.init), port.sig), None),
        };
        let sends = if s.ty.is_bun() { "its bundle".to_string() } else { t.name(port.sig).to_string() };
        let label = port.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default();
        let role = if outputs_west {
            Role::OutputGate { name: port.name.clone() }
        } else {
            Role::OutputPort { name: port.name.clone(), signal: port.sig }
        };
        let id = cg.net.add(kind, role);
        let e = &mut cg.net.entities[id];
        e.dir = Dir::East;
        e.description = Some(if outputs_west {
            format!("Ticky output `{}` (gate): its result runs on a line of poles to the output port at the west edge.", port.name)
        } else {
            format!("Ticky output `{}` ({}){label}: sends {sends} on wires connected to this combinator's output (right) side.", port.name, port.ty.name())
        });
        cg.nets[0].members.push((id, Conn::InGreen));
        if let Some(x) = reads {
            cg.bread(x, id, false);
        }
        port_ents[pi] = id;
        if outputs_west {
            // The output port proper: passes on what arrives on its line (red).
            let pass = if s.ty.is_bun() { each } else { port.sig };
            let a = Arith { first: Operand::Sig(pass), first_nets: Nets::RED, second: Operand::Const(0), second_nets: Nets::BOTH, op: ArOp::Add, out: pass };
            let out = cg.net.add(Kind::Arith(a), Role::OutputPort { name: port.name.clone(), signal: port.sig });
            let e = &mut cg.net.entities[out];
            e.dir = Dir::West;
            e.description = Some(format!(
                "Ticky output `{}` ({}){label}: sends {sends} on wires connected to this combinator's output (left) side.",
                port.name,
                port.ty.name(),
            ));
            port_ents[pi] = out;
        }
    }
}

/// Each screen's lamps (or its speaker or panel), pixel by pixel.
pub(super) fn screens(cg: &mut Cg, p: &Program, shared: &Shared) -> Vec<Vec<EntId>> {
    // Screens: a lamp per pixel on its bank's wire, showing the pixel's signal (packed RGB),
    // off while it's 0.
    let mut screen_lamps = Vec::new();
    for (k, sc) in p.screens.iter().enumerate() {
        let bs = crate::expand::bank_size();
        let mut lamps = Vec::new();
        for b in 0..sc.pixels().div_ceil(bs) {
            let bank = format!("{}#{b}", sc.var);
            let reg = p.states.iter().position(|s| s.name == bank).and_then(|si| shared.state_bun.get(&si).copied());
            if let Some(spec) = &sc.speaker {
                let sig = crate::ir::Graph::slot(0);
                let id = cg.net.add(Kind::Speaker(ticky_factorio::netlist::Speaker { sig, ..spec.clone() }), Role::Pixel { screen: k, index: 0 });
                let label = sc.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default();
                cg.net.entities[id].description = Some(format!("Ticky speaker `{}`{label}", sc.name));
                if let Some(x) = reg {
                    cg.bread_single(x, id);
                }
                lamps.push(id);
                continue;
            }
            if let Some(spec) = &sc.panel {
                let sig = crate::ir::Graph::slot(0);
                let messages = spec.messages.iter().enumerate().map(|(k, (_, icon, text))| (k as i32 + 1, *icon, text.clone())).collect();
                let kind = Kind::Panel(ticky_factorio::netlist::Panel { sig, messages, always_show: spec.always_show, show_in_chart: spec.show_in_chart });
                let id = cg.net.add(kind, Role::Pixel { screen: k, index: 0 });
                let label = sc.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default();
                cg.net.entities[id].description = Some(format!("Ticky panel `{}`{label}", sc.name));
                if let Some(x) = reg {
                    cg.bread_single(x, id);
                }
                lamps.push(id);
                continue;
            }
            for j in 0..bs.min(sc.pixels() - b * bs) {
                let sig = crate::ir::Graph::slot(j);
                let i = b * bs + j;
                let id = cg.net.add(Kind::Lamp(c(sig, CmpOp::Ne, 0), Some(sig)), Role::Pixel { screen: k, index: i });
                let label = sc.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default();
                cg.net.entities[id].description = Some(format!("Ticky screen `{}`{label}: pixel ({}, {})", sc.name, i % sc.w, i / sc.w));
                if let Some(x) = reg {
                    cg.bread_single(x, id);
                }
                lamps.push(id);
            }
        }
        screen_lamps.push(lamps);
    }
    screen_lamps
}
