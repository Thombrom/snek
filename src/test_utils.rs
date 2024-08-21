use std::{collections::HashMap, io::BufRead, path::{Path, PathBuf}, process::Output};

use anyhow::bail;
use itertools::Itertools;
use serde::{de::{Visitor, Error}, Deserialize, Serialize};

use crate::parser::SnekError;

#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged)]
pub enum TestOutput {
    Something(String), // Implies that we don't care about the thing
    Number(f64),
    List(Vec<TestOutput>)
}
pub struct EvaluationResult(Result<TestOutput, SnekError>);

impl From<EvaluationResult> for Result<TestOutput, SnekError> {
    fn from(value: EvaluationResult) -> Self {
        value.0
    }
}

struct EvaluationResultVisitor {}

impl<'de> Deserialize<'de> for EvaluationResult {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de> {
        
        deserializer.deserialize_map(EvaluationResultVisitor {})
    }
}

impl<'de> Visitor<'de> for EvaluationResultVisitor {
    type Value = EvaluationResult;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "A structure containing the boolean key 'ok'. If it's okay, contains the key 'output', otherwise the key 'type'")
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
        where
            A: serde::de::MapAccess<'de>, {
        
        if map.next_key::<String>()? != Some("ok".to_owned()) {
            return Err(A::Error::custom("First key should be 'ok'"))
        }

        let ok: bool = map.next_value()?;
        let result = if ok {
            if map.next_key::<String>()?.as_ref()
                .ok_or(A::Error::custom("Must have two keys"))? != "output" 
            {
                return Err(A::Error::custom("Second ok key should be 'output'"))
            }

            let value: TestOutput = map.next_value()?;
            Ok(EvaluationResult(Ok(value)))
        } else {
            if map.next_key::<String>()?.as_ref()
                .ok_or(A::Error::custom("Must have two keys"))? != "type" 
            {
                return Err(A::Error::custom("Second ok key should be 'type'"))
            }

            let error = match map.next_value::<String>()?.as_ref() {
                "SnekEvaluationError" => SnekError::SnekEvaluationError,
                "SnekSyntaxError" => SnekError::SnekSyntaxError,
                "SnekNameError" => SnekError::SnekNameError,
                other => return Err(A::Error::custom(format!("Unrecognized snek error: {}", other)))
            };
            Ok(EvaluationResult(Err(error)))
        };

        if map.next_key::<String>()? != None {
            return Err(A::Error::custom("Only two keys should be present"));
        }

        result
    }
}

fn load_input_file<P: AsRef<Path>>(path: P) -> anyhow::Result<Vec<String>> {
    let source = std::fs::read(path)?;
    Ok(source.lines().collect::<Result<Vec<String>, _>>()?)
}

fn load_output_file<P: AsRef<Path>>(path: P) -> anyhow::Result<Vec<EvaluationResult>> {
    let source = std::fs::read(path)?;
    let result: Vec<EvaluationResult> = serde_json::from_slice(&source)?;
    Ok(result)
}

pub fn load_test_pair(testcase: usize) -> anyhow::Result<Vec<(String, EvaluationResult)>> {
    if testcase < 13 || testcase > 72 { bail!("Testcase out of bounds"); }

    let base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let input = load_input_file(base_path.join("test_inputs").join(format!("{}.snek", testcase)))?;
    let output = load_output_file(base_path.join("test_outputs").join(format!("{}.json", testcase)))?;

    if input.len() != output.len() { bail!("Input and output of testcase does not match"); }
    Ok(input.into_iter().zip(output.into_iter()).collect_vec())
}

pub fn all_testcases() -> impl Iterator<Item = usize> {
    let mut testcases = (13..=55).collect_vec();
    testcases.extend(61..=72);

    testcases.into_iter()    
}