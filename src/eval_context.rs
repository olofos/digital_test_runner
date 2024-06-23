use crate::{framed_map::FramedMap, DataEntry, InputValue};
use rand::{rngs::StdRng, Rng, SeedableRng};
use std::{cell::RefCell, collections::HashMap};

#[derive(Debug)]
pub struct EvalContext {
    vars: FramedMap<String, i64>,
    outputs: HashMap<String, InputValue>,
    rng: RefCell<StdRng>,
    seed: u64,
}

impl EvalContext {
    pub fn new() -> Self {
        let mut seed_bytes: [u8; 8] = Default::default();
        getrandom::getrandom(&mut seed_bytes).unwrap();
        let seed = u64::from_le_bytes(seed_bytes);

        Self::with_seed(seed)
    }

    pub fn with_seed(seed: u64) -> Self {
        Self {
            vars: FramedMap::new(),
            outputs: HashMap::new(),
            rng: RefCell::new(StdRng::seed_from_u64(seed)),
            seed,
        }
    }

    pub fn push_frame(&mut self) {
        self.vars.push_frame()
    }

    pub fn pop_frame(&mut self) {
        self.vars.pop_frame()
    }

    pub fn set(&mut self, name: &str, value: i64) {
        self.vars.set(name, value)
    }

    pub fn get(&self, name: &str) -> Option<i64> {
        if let Some(n) = self.vars.get(name) {
            Some(n)
        } else {
            match self.outputs.get(name)? {
                InputValue::Value(n) => Some(*n),
                InputValue::Z => None,
            }
        }
    }

    pub fn set_outputs(&mut self, outputs: Vec<DataEntry<'_, InputValue>>) {
        self.outputs = outputs
            .into_iter()
            .map(|entry| (entry.signal.name.to_string(), entry.value))
            .collect();
    }

    pub fn reset_random_seed(&mut self) {
        self.rng = RefCell::new(StdRng::seed_from_u64(self.seed));
    }

    pub fn random<R: rand::distributions::uniform::SampleRange<i64>>(&self, range: R) -> i64 {
        self.rng.borrow_mut().gen_range(range)
    }
}

impl Default for EvalContext {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eval_context_works() {
        let mut ctx = EvalContext::new();
        ctx.set("a", 1);
        ctx.set("b", 2);
        ctx.set("c", 3);
        assert_eq!(ctx.get("a"), Some(1));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
        ctx.set("a", 4);
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));

        ctx.push_frame();
        ctx.set("a", 5);
        ctx.set("b", 6);
        assert_eq!(ctx.get("a"), Some(5));
        assert_eq!(ctx.get("b"), Some(6));
        assert_eq!(ctx.get("c"), Some(3));

        ctx.pop_frame();
        assert_eq!(ctx.get("a"), Some(4));
        assert_eq!(ctx.get("b"), Some(2));
        assert_eq!(ctx.get("c"), Some(3));
    }
}
