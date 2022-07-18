fn initialize_logging() {
    env_logger::init();
}

fn main() {
    initialize_logging();
    riscverifier::process_commands();
}
