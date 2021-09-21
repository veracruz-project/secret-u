
SHELL = /bin/bash

# environment variables, we prefer speed over portability
override ENV += RUSTFLAGS=-Ctarget-cpu=native
# needed to compile large bitslice arrays, the generated
# expressions tend to overflow the stack
override ENV += RUST_MIN_STACK=16777216


.PHONY: all build
all build:
	$(ENV) cargo build --features u262144,x32768

# note you may need to increase the default stack size to run some
# of the heavier examples
#
# ulimit -s 131072
#
.PHONY: test
define TEST_EXAMPLE
	$(ENV) cargo run --example $(1) --features u262144,x32768

endef
test:
	$(ENV) cargo test --lib --features u262144,x32768 -- --nocapture --test-threads 1
	$(ENV) cargo build --lib --no-default-features
	$(patsubst examples/%.rs,$(call TEST_EXAMPLE,%),$(wildcard examples/*.rs))

# quick test only tests up to u512 and does not test examples
quick-test:
	$(ENV) cargo test --lib --features u512,x64 -- --nocapture --test-threads 1

.PHONY: bench-sha256
bench-sha256:
	# build (assuming builds are cached)
	$(ENV) cargo build --release --features u262144,x32768 --example sha256_reference
	$(ENV) cargo build --release --features u262144,x32768 --example sha256
	$(ENV) cargo build --release --features u262144,x32768 --example sha256_fast
	# run, measuring execution time
	time ./target/release/examples/sha256_reference <(cat $$(find -name '*.rs'))
	time ./target/release/examples/sha256 			<(cat $$(find -name '*.rs'))
	time ./target/release/examples/sha256_fast 		<(cat $$(find -name '*.rs'))

.PHONY: bench-aes
bench-aes:
	# build (assuming builds are cached)
	$(ENV) cargo build --release --features u262144,x32768 --example aes_reference
	$(ENV) cargo build --release --features u262144,x32768 --example aes
	cp target/release/examples/aes target/release/examples/aes_shuffle
	$(ENV) cargo build --release --features u262144,x32768 --example aes --features example-bitslice-tables
	cp target/release/examples/aes target/release/examples/aes_bitslice
	$(ENV) cargo build --release --features u262144,x32768 --example aes_more_simd
	cp target/release/examples/aes_more_simd target/release/examples/aes_more_simd_shuffle
	$(ENV) cargo build --release --features u262144,x32768 --example aes_more_simd --features example-bitslice-tables
	cp target/release/examples/aes_more_simd target/release/examples/aes_more_simd_bitslice
	# run, measuring execution time
	$(strip \
		time ./target/release/examples/aes_reference \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "000102030405060708090a0b0c0d0e0f" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test_reference.encrypted)
	$(strip \
		time ./target/release/examples/aes_shuffle \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "000102030405060708090a0b0c0d0e0f" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test_shuffle.encrypted)
	$(strip \
		time ./target/release/examples/aes_bitslice \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "000102030405060708090a0b0c0d0e0f" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test_bitslice.encrypted)
	$(strip \
		time ./target/release/examples/aes_more_simd_shuffle \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "000102030405060708090a0b0c0d0e0f" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test_shuffle.encrypted)
	$(strip \
		time ./target/release/examples/aes_more_simd_bitslice \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "000102030405060708090a0b0c0d0e0f" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test_bitslice.encrypted)

.PHONY: bench-chacha20
bench-chacha20:
	# build (assuming builds are cached)
	$(ENV) cargo build --release --features u262144,x32768 --example chacha20_reference
	$(ENV) cargo build --release --features u262144,x32768 --example chacha20
	$(ENV) cargo build --release --features u262144,x32768 --example chacha20_simd
	# run, measuring execution time
	$(strip \
		time ./target/release/examples/chacha20_reference \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "0001020304050607" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test_reference.encrypted)
	$(strip \
		time ./target/release/examples/chacha20 \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "0001020304050607" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test.encrypted)
	$(strip \
		time ./target/release/examples/chacha20_simd \
		<(echo "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" | xxd -r -p) \
		<(echo "0001020304050607" | xxd -r -p) \
		<(cat $$(find -name '*.rs')) \
		target/test_simd.encrypted)

.PHONY: bench-sss
bench-sss:
	# build (need to move so different configurations don't overwrite each other)
	$(ENV) cargo build --release --features u262144,x32768 --example sss
	$(ENV) cargo build --release --features u262144,x32768 --example sss_simd
	cp target/release/examples/sss 	    target/release/examples/sss_shuffle
	cp target/release/examples/sss_simd target/release/examples/sss_simd_shuffle
	$(ENV) cargo build --release --features u262144,x32768 --example sss      --features example-bitslice-tables
	$(ENV) cargo build --release --features u262144,x32768 --example sss_simd --features example-bitslice-tables
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
