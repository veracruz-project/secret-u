
SHELL = /bin/bash

.PHONY: all build
all build:
	cargo build

# note you may need to increase the default stack size to run some
# of the heavier examples
#
# ulimit -s 131072
#
.PHONY: test
define TEST_EXAMPLE
	cargo run --example $(1)

endef
test:
	cargo test --lib -- --nocapture --test-threads 1
	cargo build --lib --no-default-features
	$(patsubst examples/%.rs,$(call TEST_EXAMPLE,%),$(wildcard examples/*.rs))

.PHONY: bench-sha256
bench-sha256:
	# build (assuming builds are cached)
	cargo build --release --example sha256_reference
	cargo build --release --example sha256_fast
	cargo build --release --example sha256
	# run, measuring execution time
	time cargo run --release --example sha256_reference -- <(cat $$(find -name '*.rs'))
	time cargo run --release --example sha256_fast 		-- <(cat $$(find -name '*.rs'))
	time cargo run --release --example sha256 			-- <(cat $$(find -name '*.rs'))

.PHONY: bench-sss
bench-sss:
	# build (need to move so different configurations don't overwrite each other)
	cargo build --release --example sss		 --features debug-cycle-count
	cargo build --release --example sss_simd --features debug-cycle-count
	cp target/release/examples/sss 	    target/release/examples/sss_shuffle
	cp target/release/examples/sss_simd target/release/examples/sss_simd_shuffle
	$(strip RUSTFLAGS="-C lto=no" \
		cargo build -v --release --example sss \
			--features debug-cycle-count,example-bitslice-tables )
	$(strip RUSTFLAGS="-C lto=no" \
		cargo build -v --release --example sss_simd \
			--features debug-cycle-count,example-bitslice-tables )
	cp target/release/examples/sss 	    target/release/examples/sss_bitslice
	cp target/release/examples/sss_simd target/release/examples/sss_simd_bitslice
	# run, measuring execution time
	time ./target/release/examples/sss_shuffle
	time ./target/release/examples/sss_simd_shuffle
	time ./target/release/examples/sss_bitslice
	time ./target/release/examples/sss_simd_bitslice

.PHONY: clean
clean:
	cargo clean
