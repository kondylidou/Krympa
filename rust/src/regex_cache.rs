use regex::Regex;
use std::cell::RefCell;
use std::collections::HashMap;

thread_local! {
    static CACHE: RefCell<HashMap<String, Regex>> = RefCell::new(HashMap::new());
}

/// Return the compiled regex for `pattern`, compiling it at most once per thread.
///
/// Compiling a regex is orders of magnitude slower than running one, and the
/// formula-matching and proof-trimming code builds its patterns on every call
/// (many of them from variable or lemma names). Without this cache, regex
/// compilation dominates the CPU time of `minimize`.
///
/// Panics if `pattern` is not a valid regex, like `Regex::new(..).unwrap()`.
pub fn cached_regex(pattern: &str) -> Regex {
    CACHE.with(|cache| {
        if let Some(re) = cache.borrow().get(pattern) {
            return re.clone();
        }
        let re = Regex::new(pattern).unwrap();
        cache.borrow_mut().insert(pattern.to_string(), re.clone());
        re
    })
}
