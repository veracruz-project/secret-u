
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
# ulimit -s 1073741824
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

.PHONY: bench-rsa
bench-rsa:
	# build (assuming builds are cached)
	$(ENV) cargo build --release --features u262144,x32768 --example rsa
	# run measuring execution time
	$(strip \
		time ./target/release/examples/rsa \
		encrypt \
		<(echo "b418303ccf29da5dc43fc537ffd60be9008a8e5b663dfc00a244f1cacff13aecc9a3c4bcb2e247f580f98234372c5f26466deb7005e9fe15f710ad6109bbbcb5c0d28cb34cf5945b03277e5b459816d258b2af28faf339e287b0b468f75df8094376f38abc8b30a66a24b4167546d87ab724e4772f81f84bc2b6bd6f9928f97cb531aadf43e37b6ebc4bfd7b616711f06c83aa0fb0144fae379e236db21b8f0562f60c65b928fb3ca5f6fb722394a4b229db5076829bd86c6d22d03040dadfdad72edf753582b8a429c746966dd5ccb31a0a3c951d2e318585afe6d58de16de1079606c4f9c36e37f8f74a0f1fe28aa98473acd3b779b1860e41849a3d4eef6d" | xxd -r -p) \
		<(echo "7f0ef5b1614318f1c08c713ae1ff84a59da123706e80dab323c8da8209151b4a85b44a100b70c3edfc518c400491048c3f723b81ec5a3ace0a6234c05a9a9e37e8d3633af8d7e61413f4a01c0acc938551d8b6e585af662e612715115d3c69cb3752cbde1cc962c875e87139cb01f1a71a6127e2c29cc2adc8b11e93868e36fd4a625aed7aef238cb89fb47013ce9c96074e3ffe890e567217eddd27045dcafd1ec8a5c0c127ed8c13889a07368309bd37d680a641e267b7a7ff8ea6d95db08baec52f59b81f230f5f796a00d3f61769691952d959ba8aa7cfda01ae2985d968df444d228079d0d7f1b97b30e0a592dc94233cec553c68b38c20a7cdf049c58d" | xxd -r -p) \
		Cargo.toml \
		target/test_rsa.encrypted)

.PHONY: clean
clean:
	cargo clean
