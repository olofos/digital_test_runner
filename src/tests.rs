#![cfg(test)]

use super::*;
use errors::{RuntimeError, SignalError, SignalErrorKind};
use static_test::Driver;

struct TableDriver<'a> {
    outputs: Vec<Vec<OutputEntry<'a>>>,
}

struct ConstDriver<'a> {
    outputs: Vec<OutputEntry<'a>>,
}

#[derive(Debug, thiserror::Error)]
#[error("Error")]
struct DriverError;

impl<'a> TestDriver for TableDriver<'a> {
    type Error = DriverError;

    fn write_input_and_read_output(
        &mut self,
        _inputs: &[InputEntry<'_>],
    ) -> Result<Vec<OutputEntry<'_>>, Self::Error> {
        self.outputs.pop().ok_or(DriverError)
    }
}

impl<'a> TableDriver<'a> {
    fn new(data: &[Vec<(&'a Signal, i64)>]) -> Self {
        let mut outputs: Vec<Vec<OutputEntry<'a>>> = data
            .iter()
            .map(|row| {
                row.iter()
                    .map(|(signal, value)| OutputEntry {
                        signal,
                        value: (*value).into(),
                    })
                    .collect()
            })
            .collect();
        outputs.reverse();
        Self { outputs }
    }
}

impl<'a> TestDriver for ConstDriver<'a> {
    type Error = DriverError;

    fn write_input_and_read_output(
        &mut self,
        _inputs: &[InputEntry<'_>],
    ) -> Result<Vec<OutputEntry<'_>>, Self::Error> {
        Ok(self.outputs.clone())
    }
}

#[test]
fn run_works() -> miette::Result<()> {
    let input = r"
BUS-CLK S         A        B        N ALU-~RESET ALU-AUX   OUT           FLAG DLEN DSUM

let ADD = 0;
let OR  = 1;
let XOR = 2;
let AND = 3;

0       0         0        0        0 0          0         X             X    X    X
0       0         0        0        0 1          0         X             X    X    X

loop (a,2)
loop (b,2)
0       (OR)      (a)      (b)      0 1          0         (a|b)         X    X    X
0       (AND)     (a)      (b)      0 1          0         (a&b)         X    X    X
0       (XOR)     (a)      (b)      0 1          0         (a^b)         X    X    X
0       (ADD)     (a)      (b)      0 1          0         (a+b)         X    X    X
end loop
end loop

";
    let known_inputs = ["BUS-CLK", "S", "A", "B", "N", "ALU-~RESET", "ALU-AUX"]
        .into_iter()
        .map(|name| Signal {
            name: String::from(name),
            bits: 1,
            typ: SignalType::Input {
                default: InputValue::Value(0),
            },
        });
    let known_outputs = ["OUT", "FLAG", "DLEN", "DSUM"]
        .into_iter()
        .map(|name| Signal {
            name: String::from(name),
            bits: 1,
            typ: SignalType::Output,
        })
        .collect::<Vec<_>>();
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;
    let mut driver = Driver;
    let it = testcase.try_iter(&mut driver)?;
    for row in it {
        let row = row.unwrap();
        for input in row.inputs {
            print!("{} ", input.value);
        }
        print!("| ");
        for output in row.outputs {
            print!("{} ", output.expected);
        }
        println!()
    }

    Ok(())
}

#[test]
fn can_parse_directional_signal() -> miette::Result<()> {
    let input = r"
A A_out
1 X
Z 1";
    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Bidirectional {
            default: InputValue::Value(0),
        },
    });

    let known_signals = Vec::from_iter(known_inputs);
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

    let mut driver = ConstDriver {
        outputs: vec![OutputEntry {
            signal: &known_signals[0],
            value: OutputValue::Value(0),
        }],
    };
    let it = testcase.try_iter(&mut driver)?;
    let result: Vec<_> = it.collect::<Result<_, _>>().unwrap();

    assert_eq!(result.len(), 2);
    assert_eq!(result[0].inputs[0].signal.name, "A");
    assert_eq!(result[0].outputs[0].signal.name, "A");
    assert_eq!(result[1].inputs[0].signal.name, "A");
    assert_eq!(result[1].outputs[0].signal.name, "A");

    assert_eq!(result[0].inputs[0].value, InputValue::Value(1));
    assert_eq!(result[0].outputs[0].expected, ExpectedValue::X);

    assert_eq!(result[1].inputs[0].value, InputValue::Z);
    assert_eq!(result[1].outputs[0].expected, ExpectedValue::Value(1));

    Ok(())
}

#[test]
fn iter_with_c_works() -> miette::Result<()> {
    let input = r"
    CLK IN OUT
    C 0 0
    ";

    let expanded_input = r"
    CLK IN OUT
    0 0 X
    1 0 X
    0 0 0
    ";
    let known_inputs = ["CLK", "IN"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["OUT"]
        .into_iter()
        .map(|name| Signal {
            name: String::from(name),
            bits: 1,
            typ: SignalType::Output,
        })
        .collect::<Vec<_>>();
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

    let expanded_testcase =
        ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

    let mut driver = Driver;
    let rows = testcase
        .try_iter(&mut driver)?
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    let expanded_rows: Vec<_> = expanded_testcase
        .try_iter(&mut driver)?
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    for (row, expanded) in rows.into_iter().zip(expanded_rows) {
        assert_eq!(row.inputs, expanded.inputs);
        for (got, expected) in row.outputs.into_iter().zip(expanded.outputs) {
            assert_eq!(got.expected, expected.expected);
        }
    }

    Ok(())
}

#[test]
fn iter_with_x_works() -> miette::Result<()> {
    let input = r"
    A B OUT
    X X 0
    ";

    let expanded_input = r"
    A B OUT
    0 0 0
    1 0 0
    0 1 0
    1 1 0
    ";
    let known_inputs = ["A", "B"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["OUT"]
        .into_iter()
        .map(|name| Signal {
            name: String::from(name),
            bits: 1,
            typ: SignalType::Output,
        })
        .collect::<Vec<_>>();
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

    let expanded_testcase =
        ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

    let mut driver = Driver;
    let rows = testcase
        .try_iter(&mut driver)?
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    let expanded_rows: Vec<_> = expanded_testcase
        .try_iter(&mut driver)?
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    for (row, expanded) in rows.into_iter().zip(expanded_rows) {
        assert_eq!(row.inputs, expanded.inputs);
        for (got, expected) in row.outputs.into_iter().zip(expanded.outputs) {
            assert_eq!(got.expected, expected.expected);
        }
    }
    Ok(())
}

#[test]
fn iter_with_x_and_c_works() -> miette::Result<()> {
    let input = r"
    CLK A OUT
    C X 0
    ";

    let expanded_input = r"
    CLK A OUT
    0 0 X
    1 0 X
    0 0 0
    0 1 X
    1 1 X
    0 1 0
    ";
    let known_inputs = ["CLK", "A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["OUT"]
        .into_iter()
        .map(|name| Signal {
            name: String::from(name),
            bits: 1,
            typ: SignalType::Output,
        })
        .collect::<Vec<_>>();
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs.clone()));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

    let expanded_testcase =
        ParsedTestCase::from_str(expanded_input)?.with_signals(known_signals)?;

    let mut driver = Driver;
    let rows = testcase
        .try_iter(&mut driver)?
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    let expanded_rows: Vec<_> = expanded_testcase
        .try_iter(&mut driver)?
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    for (row, expanded) in rows.into_iter().zip(expanded_rows) {
        assert_eq!(row.inputs, expanded.inputs);
        for (got, expected) in row.outputs.into_iter().zip(expanded.outputs) {
            assert_eq!(got.expected, expected.expected);
        }
    }

    Ok(())
}

#[test]
fn with_signals_returns_error_for_missing_signal() -> miette::Result<()> {
    let input = r"
    A B C
    0 0 0
    ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase_result = ParsedTestCase::from_str(input)?.with_signals(known_signals);

    assert!(testcase_result.is_err());

    Ok(())
}

#[test]
fn works_if_not_all_outputs_are_given() -> miette::Result<()> {
    let input = r"
    A B C
    0 0 0
    0 0 0
    ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

    let signal = Signal {
        name: String::from("B"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal = &signal;

    let mut driver = TableDriver::new(&[vec![(signal, 0)], vec![(signal, 0)], vec![(signal, 0)]]);

    for row in testcase.try_iter(&mut driver)? {
        let _ = row.unwrap();
    }

    Ok(())
}

#[test]
fn gives_error_if_outputs_change_order() -> miette::Result<()> {
    let input = r"
    A B C
    0 0 1
    1 1 0
    ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

    let signal_b = Signal {
        name: String::from("B"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal_b = &signal_b;

    let signal_c = Signal {
        name: String::from("C"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal_c = &signal_c;

    let mut driver = TableDriver::new(&[
        vec![(signal_b, 0), (signal_c, 1)],
        vec![(signal_c, 0), (signal_b, 1)],
    ]);

    let mut it = testcase.try_iter(&mut driver)?;
    assert!(it.next().unwrap().is_err());

    Ok(())
}

#[test]
fn gives_error_if_outputs_changes_length() -> miette::Result<()> {
    let input = r"
    A B C
    0 0 1
    1 1 0
    ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

    let signal_b = Signal {
        name: String::from("B"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal_b = &signal_b;

    let signal_c = Signal {
        name: String::from("C"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal_c = &signal_c;

    let mut driver = TableDriver::new(&[vec![(signal_b, 0), (signal_c, 1)], vec![(signal_b, 0)]]);

    let mut it = testcase.try_iter(&mut driver)?;
    assert!(it.next().unwrap().is_err());

    Ok(())
}

#[test]
fn gives_error_if_outputs_changes_length_2() -> miette::Result<()> {
    let input = r"
    A B C
    0 0 1
    1 1 0
    ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

    let signal_b = Signal {
        name: String::from("B"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal_b = &signal_b;

    let signal_c = Signal {
        name: String::from("C"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal_c = &signal_c;

    let mut driver = TableDriver::new(&[vec![(signal_b, 0)], vec![(signal_b, 0), (signal_c, 1)]]);

    let mut it = testcase.try_iter(&mut driver)?;
    assert!(it.next().unwrap().is_err());

    Ok(())
}

#[test]
fn gives_error_for_c_if_not_an_input() -> miette::Result<()> {
    let input = r"
    A B
    0 c
";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let Err(err) = ParsedTestCase::from_str(input)?.with_signals(known_signals) else {
        panic!("Should have failed")
    };

    assert!(matches!(err.0, SignalErrorKind::NotAnInput { .. }));

    Ok(())
}

#[test]
fn gives_error_for_reading_value_if_not_an_output() -> miette::Result<()> {
    let input = r"
    A B
    0 (A)
";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let Err(err) = ParsedTestCase::from_str(input)?.with_signals(known_signals) else {
        panic!("Should have failed")
    };

    assert!(matches!(err.0, SignalErrorKind::NotAnOutput { .. }));

    Ok(())
}

#[test]
fn test_missing_output() -> miette::Result<()> {
    let input = r"
A B C
0 X X
1 X (B)";
    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

    let mut driver = Driver;
    let Err(err) = testcase.try_iter(&mut driver) else {
        panic!("Should have failed")
    };
    assert!(matches!(
        err,
        IterationError::Runtime(RuntimeError(
            errors::RuntimeErrorKind::MissingOutputs { .. }
        ))
    ));

    Ok(())
}

#[test]
fn return_z_for_read_signal_should_not_panic() -> miette::Result<()> {
    let input = r"
    A B C
    0 0 0
    1 1 (B)
    ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals)?;

    let signal_b = Signal {
        name: String::from("B"),
        bits: 1,
        typ: SignalType::Output,
    };
    let signal_b = &signal_b;

    let mut driver = ConstDriver {
        outputs: vec![OutputEntry {
            signal: signal_b,
            value: OutputValue::Z,
        }],
    };

    let Err(err) = testcase
        .try_iter(&mut driver)?
        .collect::<Result<Vec<_>, _>>()
    else {
        panic!("Expected an error")
    };

    let IterationError::Runtime(RuntimeError(errors::RuntimeErrorKind::ExprError(
        errors::ExprError(errors::ExprErrorKind::UnexpectedValueForSignal(err_name, err_val)),
    ))) = err
    else {
        panic!("Unexpected error type")
    };
    assert_eq!(err_name, String::from("B"));
    assert_eq!(err_val, OutputValue::Z);

    Ok(())
}

#[test]
fn with_error_with_duplicate_signal_gives_error() -> miette::Result<()> {
    let input = r"
    A B
    0 0
    1 1
    ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let Err(err) = ParsedTestCase::from_str(input)?.with_signals(known_signals) else {
        panic!("Expected an error")
    };
    assert!(matches!(
        err,
        SignalError(SignalErrorKind::DuplicateSignal { .. })
    ));

    Ok(())
}

#[test]
fn virtual_signal_and_signal_with_same_name_should_give_error() -> miette::Result<()> {
    let input = r"
        A B C
        declare C = !B;
        x x x
        ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B", "C"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let Err(_) = ParsedTestCase::from_str(input)?.with_signals(known_signals) else {
        panic!("Expected an error")
    };

    Ok(())
}

#[test]
fn virtual_signal_ignores_variables() -> miette::Result<()> {
    let input = r"
        A B C
        declare C = !B;
        let B = 2;
        0 x 1
        ";

    let known_inputs = ["A"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Input {
            default: InputValue::Value(0),
        },
    });
    let known_outputs = ["B"].into_iter().map(|name| Signal {
        name: String::from(name),
        bits: 1,
        typ: SignalType::Output,
    });
    let known_signals = Vec::from_iter(known_inputs.chain(known_outputs));
    let testcase = ParsedTestCase::from_str(input)?.with_signals(known_signals.clone())?;

    let mut driver = ConstDriver {
        outputs: vec![OutputEntry {
            signal: &known_signals[1],
            value: OutputValue::Value(0),
        }],
    };
    let it = testcase.try_iter(&mut driver)?;
    let result: Vec<_> = it.collect::<Result<_, _>>()?;
    assert!(&result[0].outputs[1].check());

    Ok(())
}
