#!/bin/bash
set -e  # Exit immediately if a command fails

echo "=== Starting Independent Reproduction Audit ==="
echo "Date: $(date)"
echo "Host: $(hostname)"

# 1. System Info
echo "--- System Information ---"
uname -a
python3 --version

# 2. Virtual Environment Setup
echo "--- Setting up Virtual Environment ---"
# Check if venv exists, if not create it
if [ ! -d "venv" ]; then
    python3 -m venv venv
fi
source venv/bin/activate

ARCH=$(uname -m)
if [ "$ARCH" != "x86_64" ] && [ "$ARCH" != "amd64" ]; then
    echo "Unsupported architecture for this audit: $ARCH"
    echo "python-flint wheels are only published for x86_64; please use an x86_64/amd64 instance."
    exit 2
fi

pip install --upgrade pip
pip install -r requirements.txt

# 3. Run the Verification (The "Load Bearing" Artifacts)
# Note: These commands match the ones in your paper's audit manifest.

echo "--- 1/2: Verifying Low-Height Zeta Non-Vanishing (Left Rectangle) ---"
python3 verify_attachment_arb.py \
  --zeta-certify \
  --rect-sigma-min 0.6 --rect-sigma-max 0.7 \
  --rect-t-min 0.0 --rect-t-max 20.0 \
  --theta-init-n-sigma 10 --theta-init-n-t 50 \
  --theta-min-sigma-width 0.0001 --theta-min-t-width 0.001 \
  --theta-max-boxes 500000 \
  --theta-time-limit 0 \
  --prec 260 \
  --zeta-out audit_zeta_left.json \
  --progress

echo "--- 2/2: Verifying Low-Height Zeta Non-Vanishing (Right Rectangle) ---"
python3 verify_attachment_arb.py \
  --zeta-certify \
  --rect-sigma-min 0.7 --rect-sigma-max 0.999 \
  --rect-t-min 0.0 --rect-t-max 20.0 \
  --theta-init-n-sigma 10 --theta-init-n-t 50 \
  --theta-min-sigma-width 0.0001 --theta-min-t-width 0.001 \
  --theta-max-boxes 500000 \
  --theta-time-limit 0 \
  --prec 260 \
  --zeta-out audit_zeta_right.json \
  --progress

echo "=== Audit Complete: SUCCESS ==="
