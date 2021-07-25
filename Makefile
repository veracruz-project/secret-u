
all build:
	cargo build

run:
	cargo run

test:
	cargo build --no-default-features 
	cargo test --lib --features debug-trace,debug-proc-macros -- --nocapture --test-threads 1
	$(patsubst \
		examples/%.rs,cargo run --example % && ,\
		$(wildcard examples/*.rs)) true

clean:
	cargo clean
