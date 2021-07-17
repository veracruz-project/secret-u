
all build:
	cargo build

run:
	cargo run

test:
	cargo build --no-default-features 
	cargo test --lib --features debug-trace,debug-proc-macro -- --nocapture --test-threads 1
	$(patsubst \
		examples/%.rs,cargo run --example % ;,\
		$(filter-out examples/sha256.rs,$(wildcard examples/*.rs)))

clean:
	cargo clean
