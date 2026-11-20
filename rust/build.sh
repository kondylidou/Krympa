#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Release build: Krympa spends real CPU time on formula matching and proof
# parsing, and an unoptimized build makes `minimize` several times slower.
cargo build --release --bin benchmarking
cargo build --release --bin krympa

cp -f target/release/benchmarking ./benchmarking_binary
cp -f target/release/krympa ./krympa

chmod +x ./benchmarking_binary ./krympa

echo "Build complete:"
echo "  - $SCRIPT_DIR/benchmarking_binary"
echo "  - $SCRIPT_DIR/krympa"
