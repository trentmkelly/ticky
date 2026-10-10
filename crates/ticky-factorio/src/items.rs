//! Item data the selector combinator reports (`stack-size` and `rocket-capacity` modes),
//! dumped from the game (harness scenario `itemdump`) for the base game and for Space Age,
//! which differ for a few items.

use std::cell::Cell;
use std::collections::HashMap;
use std::sync::OnceLock;

const ITEMS_TSV: &str = include_str!("../data/items.tsv");

thread_local! {
    static SPACE_AGE: Cell<bool> = const { Cell::new(false) };
}

/// Whether item data on this thread follows Space Age (otherwise the base game). Set by the
/// compiler for each compilation.
pub fn set_space_age(on: bool) {
    SPACE_AGE.with(|q| q.set(on));
}

pub fn space_age() -> bool {
    SPACE_AGE.with(|q| q.get())
}

/// `(stack size, rocket capacity)` per item, base game then Space Age.
type Row = [Option<(i32, i32)>; 2];

fn table() -> &'static HashMap<String, Row> {
    static T: OnceLock<HashMap<String, Row>> = OnceLock::new();
    T.get_or_init(|| {
        let mut m = HashMap::new();
        for line in ITEMS_TSV.lines().filter(|l| !l.starts_with('#') && !l.is_empty()) {
            let f: Vec<&str> = line.split('\t').collect();
            let pair = |a: &str, b: &str| -> Option<(i32, i32)> { Some((a.parse().ok()?, b.parse().ok()?)) };
            m.insert(f[0].to_string(), [pair(f[1], f[2]), pair(f[3], f[4])]);
        }
        m
    })
}

fn row(item: &str) -> Option<(i32, i32)> {
    table().get(item)?[space_age() as usize]
}

/// The item's stack size (any quality), or `None` if the game has no such item.
pub fn stack_size(item: &str) -> Option<i32> {
    row(item).map(|r| r.0)
}

/// The selector's rocket capacity for the item: `None` (no output) for items that can't go
/// in a rocket or don't exist; some tools report −1.
pub fn rocket_capacity(item: &str) -> Option<i32> {
    row(item).map(|r| r.1).filter(|c| *c != 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dumped_values() {
        set_space_age(false);
        assert_eq!(stack_size("iron-plate"), Some(100));
        assert_eq!(rocket_capacity("iron-gear-wheel"), Some(1000));
        assert_eq!(rocket_capacity("rocket-silo"), None);
        assert_eq!(stack_size("space-science-pack"), Some(2000));
        assert_eq!(stack_size("tungsten-plate"), None);
        set_space_age(true);
        assert_eq!(stack_size("space-science-pack"), Some(200));
        assert_eq!(stack_size("tungsten-plate"), Some(50));
        set_space_age(false);
    }
}
