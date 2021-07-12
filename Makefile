
all build:
	cargo build

run:
	cargo run

test:
	cargo test --features trace --features debug-proc-macro -- --nocapture --test-threads 1

clean:
	cargo clean
