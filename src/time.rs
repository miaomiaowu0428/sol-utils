pub trait DurationExt {
    fn as_ms_f64(&self) -> f64;
}

impl DurationExt for std::time::Duration {
    fn as_ms_f64(&self) -> f64 {
        self.as_nanos() as f64 / 1_000_000.0
    }
}