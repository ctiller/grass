//! Canonical-encoding checks (AGENT_BUS_SCHEMA.md section 2).
//!
//! serde_json's default (non-`preserve_order`) writer gives us sorted object
//! keys, compact output, and minimal escaping "for free" wherever content
//! passes through `serde_json::Value` (its `Map` is a `BTreeMap` since this
//! crate does not enable the `preserve_order` feature). Envelope-shaped
//! top-level structures (the event envelope, `_bus/BUS.json`) instead have a
//! *fixed*, non-alphabetical field order, so their canonical form is checked
//! by comparing against `serde_json::to_string` of the typed struct (whose
//! fields serialize in declaration order) rather than through this module.
//! What no round-trip catches is Unicode normalization, so that is checked
//! explicitly here and called on every such structure's content.

use crate::error::{invalid, AbResult};
use unicode_normalization::is_nfc;

pub fn check_nfc(value: &serde_json::Value) -> AbResult<()> {
    match value {
        serde_json::Value::String(s) => {
            if !is_nfc(s) {
                return Err(invalid(format!("string is not NFC-normalized: {s:?}")));
            }
            Ok(())
        }
        serde_json::Value::Array(items) => {
            for v in items {
                check_nfc(v)?;
            }
            Ok(())
        }
        serde_json::Value::Object(map) => {
            for (k, v) in map {
                if !is_nfc(k) {
                    return Err(invalid(format!("object key is not NFC-normalized: {k:?}")));
                }
                check_nfc(v)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nfc_string_is_accepted() {
        assert!(
            check_nfc(&serde_json::json!({"a": "e\u{0301}".chars().collect::<String>()})).is_err()
        );
        assert!(check_nfc(&serde_json::json!({"a": "\u{e9}"})).is_ok());
    }

    #[test]
    fn nested_non_nfc_is_rejected() {
        let nfd = serde_json::json!({"a": ["ok", "e\u{0301}"]});
        assert!(check_nfc(&nfd).is_err());
    }
}
