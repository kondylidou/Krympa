#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

cargo build --bin benchmarking
cargo build --bin krympa

cp -f target/debug/benchmarking ./benchmarking_binary
cp -f target/debug/krympa ./krympa

chmod +x ./benchmarking_binary ./krympa

echo "Build complete:"
echo "  - $SCRIPT_DIR/benchmarking_binary"
echo "  - $SCRIPT_DIR/krympa"
