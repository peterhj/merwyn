V ?= 0
ifeq ($(V),0)
  Q := @
else
  Q :=
endif

.PHONY: all pre versions debug release test test-lang test-ir test-vm test-vmad

all: release

pre: versions

versions:
	$(Q)cargo --version > cargo.version
	$(Q)rustc --version > rustc.version

debug: pre
	cargo build

release: pre
	cargo build --release

test: pre
	RUST_TEST_THREADS=1 cargo test --release -- --nocapture

test-lang: pre
	RUST_TEST_THREADS=1 cargo test --test lang --release -- --nocapture

test-ir: pre
	RUST_TEST_THREADS=1 cargo test --test ir --release -- --nocapture

test-vm: pre
	RUST_TEST_THREADS=1 cargo test --test vm --release -- --nocapture

test-vmad: pre
	RUST_TEST_THREADS=1 cargo test --test vmad --release -- --nocapture

test-vmfix: pre
	RUST_TEST_THREADS=1 cargo test --test vmfix --release -- --nocapture
