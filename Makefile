
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

.PHONY: clean
clean:
	cargo clean
