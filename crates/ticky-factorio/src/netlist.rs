//! The physical program: entities, their settings and the wires between them.
//! This is exactly what goes into a blueprint, and exactly what the simulator runs.

use crate::ops::{ArOp, CmpOp};
use crate::signals::Sig;

pub type EntId = usize;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Operand {
    Sig(Sig),
    Const(i32),
}

/// Which input networks an operand reads.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Nets {
    pub red: bool,
    pub green: bool,
}

impl Nets {
    pub const BOTH: Nets = Nets { red: true, green: true };
    pub const RED: Nets = Nets { red: true, green: false };
    pub const GREEN: Nets = Nets { red: false, green: true };
}

#[derive(Clone, Debug)]
pub struct Arith {
    pub first: Operand,
    pub first_nets: Nets,
    pub second: Operand,
    pub second_nets: Nets,
    pub op: ArOp,
    pub out: Sig,
}

#[derive(Clone, Debug)]
pub struct Cond {
    pub first: Sig,
    pub first_nets: Nets,
    pub second: Operand,
    pub second_nets: Nets,
    pub cmp: CmpOp,
    /// Joined to the previous condition with AND (true) or OR (false). AND binds tighter.
    pub and: bool,
}

#[derive(Clone, Debug)]
pub struct DOut {
    pub sig: Sig,
    /// Copy the signal's count from the input; otherwise output `constant`.
    pub copy: bool,
    pub constant: i32,
    pub nets: Nets,
}

#[derive(Clone, Debug)]
pub struct Decider {
    pub conds: Vec<Cond>,
    pub outputs: Vec<DOut>,
}

#[derive(Clone, Debug)]
pub struct ConstComb {
    pub values: Vec<(Sig, i32)>,
    pub on: bool,
}

/// Selector combinator modes Ticky uses. It reads both input wires and has no network
/// selection.
#[derive(Clone, Debug)]
pub enum Selector {
    /// The input signal ranked `index` (0-based) by value, largest first if `max`.
    Select { max: bool, index: i32 },
    /// How many distinct signals the input has, on `out`.
    Count { out: Sig },
}

#[derive(Clone, Debug)]
pub enum Kind {
    Arith(Arith),
    Decider(Decider),
    Selector(Selector),
    Constant(ConstComb),
    Pole,
}

impl Kind {
    pub fn proto_name(&self) -> &'static str {
        match self {
            Kind::Arith(_) => "arithmetic-combinator",
            Kind::Decider(_) => "decider-combinator",
            Kind::Selector(_) => "selector-combinator",
            Kind::Constant(_) => "constant-combinator",
            Kind::Pole => "medium-electric-pole",
        }
    }

    /// Arithmetic and decider combinators have separate input and output connectors.
    pub fn is_combinator(&self) -> bool {
        matches!(self, Kind::Arith(_) | Kind::Decider(_) | Kind::Selector(_))
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Dir {
    North,
    East,
    West,
}

/// What an entity is for. Used by the simulator (ports) and the build report.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Role {
    Core,
    InputPort { name: String, signal: Sig },
    OutputPort { name: String, signal: Sig },
    /// With output return lines: the combinator that gates an output; its result runs on a
    /// line of poles to the output port.
    OutputGate { name: String },
    RunSwitch,
    Power,
}

#[derive(Clone, Debug)]
pub struct Entity {
    pub kind: Kind,
    /// Centre position in tiles; set by layout.
    pub pos: (f64, f64),
    pub dir: Dir,
    pub description: Option<String>,
    pub role: Role,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Conn {
    InRed,
    InGreen,
    OutRed,
    OutGreen,
    /// Single-sided entities (constant combinators, poles).
    Red,
    Green,
    Copper,
}

impl Conn {
    /// `defines.wire_connector_id` value used in blueprints.
    pub fn blueprint_id(self) -> u32 {
        match self {
            Conn::InRed | Conn::Red => 1,
            Conn::InGreen | Conn::Green => 2,
            Conn::OutRed => 3,
            Conn::OutGreen => 4,
            Conn::Copper => 5,
        }
    }

    pub fn is_red(self) -> bool {
        matches!(self, Conn::InRed | Conn::OutRed | Conn::Red)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Wire {
    pub a: (EntId, Conn),
    pub b: (EntId, Conn),
}

#[derive(Clone, Debug, Default)]
pub struct Netlist {
    pub entities: Vec<Entity>,
    pub wires: Vec<Wire>,
    pub label: String,
    pub description: String,
}

/// Circuit wire reach of combinators, constant combinators and medium poles (2.0.77).
pub const CIRCUIT_REACH: f64 = 9.0;
/// Medium electric pole supply radius (the supply area is 7×7).
pub const POLE_SUPPLY: f64 = 3.5;

impl Netlist {
    pub fn add(&mut self, kind: Kind, role: Role) -> EntId {
        self.entities.push(Entity { kind, pos: (0.0, 0.0), dir: Dir::North, description: None, role });
        self.entities.len() - 1
    }

    pub fn wire(&mut self, a: (EntId, Conn), b: (EntId, Conn)) {
        self.wires.push(Wire { a, b });
    }

    pub fn find_role(&self, pred: impl Fn(&Role) -> bool) -> Option<EntId> {
        self.entities.iter().position(|e| pred(&e.role))
    }

    /// Tile footprint (width, height) given the entity's direction.
    pub fn footprint(&self, id: EntId) -> (u32, u32) {
        let e = &self.entities[id];
        if e.kind.is_combinator() {
            match e.dir {
                Dir::North => (1, 2),
                Dir::East | Dir::West => (2, 1),
            }
        } else {
            (1, 1)
        }
    }

    /// Checks that no two entities overlap, wires are within reach and (if `power`) every
    /// powered entity is covered by a pole. Returns human-readable problems.
    pub fn validate(&self, power: bool) -> Vec<String> {
        let mut problems = Vec::new();
        let mut tiles = std::collections::HashMap::new();
        for (i, _) in self.entities.iter().enumerate() {
            let (w, h) = self.footprint(i);
            let (cx, cy) = self.entities[i].pos;
            let (x0, y0) = ((cx - w as f64 / 2.0).round() as i64, (cy - h as f64 / 2.0).round() as i64);
            for dx in 0..w as i64 {
                for dy in 0..h as i64 {
                    if let Some(j) = tiles.insert((x0 + dx, y0 + dy), i) {
                        problems.push(format!("entities {j} and {i} overlap at ({}, {})", x0 + dx, y0 + dy));
                    }
                }
            }
        }
        for w in &self.wires {
            let (a, b) = (self.entities[w.a.0].pos, self.entities[w.b.0].pos);
            let d = ((a.0 - b.0).powi(2) + (a.1 - b.1).powi(2)).sqrt();
            if d > CIRCUIT_REACH {
                problems.push(format!("wire {}→{} is {d:.1} tiles long", w.a.0, w.b.0));
            }
        }
        let poles: Vec<(f64, f64)> =
            self.entities.iter().filter(|e| matches!(e.kind, Kind::Pole)).map(|e| e.pos).collect();
        for (i, e) in self.entities.iter().enumerate() {
            if !power || !e.kind.is_combinator() {
                continue;
            }
            let (w, h) = self.footprint(i);
            let covered = poles.iter().any(|p| {
                (e.pos.0 - p.0).abs() < POLE_SUPPLY + w as f64 / 2.0
                    && (e.pos.1 - p.1).abs() < POLE_SUPPLY + h as f64 / 2.0
            });
            if !covered {
                problems.push(format!("entity {i} at {:?} has no power", e.pos));
            }
        }
        problems
    }
}
