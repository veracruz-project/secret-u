
all build:
	cargo build

run:
	cargo run

test:
	cargo test --features trace -- --nocapture --test-threads 1

clean:
	cargo clean
