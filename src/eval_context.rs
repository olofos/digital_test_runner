use crate::{framed_map::FramedMap, OutputEntry, OutputValue};
use rand::{rngs::StdRng, Rng, SeedableRng};
use std::{cell::RefCell, collections::HashMap};

#[derive(Debug)]
pub(crate) struct EvalContext {
    vars: FramedMap<String, i64>,
    alt_vars: FramedMap<String, i64>,
    outputs: HashMap<String, OutputValue>,
    rng: RefCell<StdRng>,
    seed: u64,
}

impl EvalContext {
    pub(crate) fn new() -> Self {
        let mut seed_bytes: [u8; 8] = Default::default();
        getrandom::getrandom(&mut seed_bytes).unwrap();
        let seed = u64::from_le_bytes(seed_bytes);

        Self::with_seed(seed)
    }

    pub(crate) fn new_with_outputs(outputs: &[OutputEntry<'_>]) -> Self {
        let mut ctx = Self::new();
        ctx.set_outputs(outputs);
        ctx
    }

    pub(crate) fn with_seed(seed: u64) -> Self {
        Self {
            vars: FramedMap::new(),
            alt_vars: FramedMap::new(),
            outputs: HashMap::new(),
            rng: RefCell::new(StdRng::seed_from_u64(seed)),
            seed,
        }
    }

    pub(crate) fn push_frame(&mut self) {
        self.vars.push_frame()
    }

    pub(crate) fn pop_frame(&mut self) {
        self.vars.pop_frame()
    }

    pub(crate) fn set(&mut self, name: &str, value: i64) {
        self.vars.set(name, value)
    }

    pub(crate) fn get(&self, name: &str) -> Option<OutputValue> {
        if let Some(n) = self.vars.get(name) {
            Some(OutputValue::Value(n))
        } else {
            self.outputs.get(name).cloned()
        }
    }

    pub(crate) fn set_outputs(&mut self, outputs: &[OutputEntry<'_>]) {
        self.outputs = outputs
            .iter()
            .map(|entry| (entry.signal.name.to_string(), entry.value))
            .collect();
    }

    pub(crate) fn reset_random_seed(&mut self) {
        self.rng = RefCell::new(StdRng::seed_from_u64(self.seed));
    }

    pub(crate) fn random<R: rand::distributions::uniform::SampleRange<i64>>(
        &self,
        range: R,
    ) -> i64 {
        self.rng.borrow_mut().gen_range(range)
    }

    pub(crate) fn vars(&self) -> HashMap<String, i64> {
        self.vars.flatten()
    }

    pub(crate) fn swap_vars(&mut self) {
        std::mem::swap(&mut self.vars, &mut self.alt_vars);
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
        assert_eq!(ctx.get("a"), Some(OutputValue::Value(1)));
        assert_eq!(ctx.get("b"), Some(OutputValue::Value(2)));
        assert_eq!(ctx.get("c"), Some(OutputValue::Value(3)));
        ctx.set("a", 4);
        assert_eq!(ctx.get("a"), Some(OutputValue::Value(4)));
        assert_eq!(ctx.get("b"), Some(OutputValue::Value(2)));
        assert_eq!(ctx.get("c"), Some(OutputValue::Value(3)));

        ctx.push_frame();
        ctx.set("a", 5);
        ctx.set("b", 6);
        assert_eq!(ctx.get("a"), Some(OutputValue::Value(5)));
        assert_eq!(ctx.get("b"), Some(OutputValue::Value(6)));
        assert_eq!(ctx.get("c"), Some(OutputValue::Value(3)));

        ctx.pop_frame();
        assert_eq!(ctx.get("a"), Some(OutputValue::Value(4)));
        assert_eq!(ctx.get("b"), Some(OutputValue::Value(2)));
        assert_eq!(ctx.get("c"), Some(OutputValue::Value(3)));
    }
}
