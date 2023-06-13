default: all

all: c0c

c0c: ../bin/c0c
../bin/c0c: release
	mkdir -p ../bin
	cp target/release/c0c ../bin/c0c



release:
	
	RUSTFLAGS='-A dead_code' cargo build  --release


debug:
	cargo build

clean:
	cargo clean
	rm -f ../bin/c0c

check:
	cargo fmt -- --check
	cargo clippy

format:
	cargo fmt

.PHONY: c0c debug release clean check

