
all build:
	cargo build

run:
	cargo run

test:
	cargo test -- --nocapture --test-threads 1

clean:
	cargo clean
