
all build:
	cargo build

run:
	cargo run

test:
	cargo build --no-default-features 
	cargo test --features debug-trace,debug-proc-macro -- --nocapture --test-threads 1

clean:
	cargo clean
