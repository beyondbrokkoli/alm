use std::sync::OnceLock;

pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("ALM_DBG").is_some())
}

#[macro_export]
macro_rules! alm_dbgln {
    ($($arg:tt)*) => {
        if $crate::debug::enabled() {
            eprintln!($($arg)*);
        }
    };
}
