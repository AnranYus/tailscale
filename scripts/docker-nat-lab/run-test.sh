#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$DIR"

run_case() {
  local mode="$1"
  echo "============================================================"
  echo "Testing TS_ENHANCED_PUNCH=${mode} (NAT4 --random-fully <-> NAT3 MASQUERADE)"
  echo "============================================================"
  TS_ENHANCED_PUNCH="$mode" docker compose down -v >/dev/null 2>&1 || true
  TS_ENHANCED_PUNCH="$mode" docker compose up -d --build >/dev/null 2>&1

  # Wait for both peers to register with testcontrol
  for i in $(seq 1 40); do
    if docker exec ts-natlab-peer-corp tailscale --socket=/tmp/tailscaled.sock status 2>/dev/null | grep -q peer-home; then
      break
    fi
    sleep 0.5
  done

  echo "--- Initial status (peer-corp) ---"
  docker exec ts-natlab-peer-corp tailscale --socket=/tmp/tailscaled.sock status

  echo "--- Running tailscale ping (15 attempts, until-direct) ---"
  docker exec ts-natlab-peer-corp tailscale --socket=/tmp/tailscaled.sock ping --c=15 --until-direct=true peer-home || true

  echo "--- Final status (peer-corp & peer-home) ---"
  docker exec ts-natlab-peer-corp tailscale --socket=/tmp/tailscaled.sock status
  docker exec ts-natlab-peer-home tailscale --socket=/tmp/tailscaled.sock status

  echo "--- Enhanced punch logs (peer-corp) ---"
  docker logs ts-natlab-peer-corp 2>&1 | grep "enhanced-punch" || echo "(none)"
  echo "--- Enhanced punch logs (peer-home) ---"
  docker logs ts-natlab-peer-home 2>&1 | grep "enhanced-punch" || echo "(none)"
}

run_case "false"
run_case "true"
