#!/usr/bin/env python3
"""
ILG rotation-curve benchmark (global-only, no per-galaxy tuning)

Implements the closed-form rotation law derived from the RS/ILG stack:

  v_rot(r) = sqrt( w_tot(r) ) * v_bar(r)
  w_tot(r) = xi * n(r) * zeta(r) * [ 1 + C_lag * ( ((g_bar+g_ext)/a0)^(-alpha)
                                              - (1+g_ext/a0)^(-alpha) ) ]

with constants:
  alpha = (1 - 1/phi)/2
  C_lag = phi^(-5)
  a0 = 1.2e-10 m s^-2

and global factors:
  n(r) = 1 + A * (1 - exp( -(r/r0)^p )), (A, r0[kpc], p) = (7, 8, 1.6)
  zeta(r): geometry (we default to 1.0; thickness corrections are small here)
  xi: threads-informed global complexity factor via f_gas proxy quintiles

Error model (identical structure to paper):
  sigma_eff^2 = sigma_obs^2 + sigma0^2 + (f * v_obs)^2
                + sigma_beam^2 + sigma_asym^2 + sigma_turb^2
  sigma0 = 10 km/s, f = 0.05, alpha_beam = 0.3
  sigma_beam = alpha_beam * b_kpc * v_obs / (r + b_kpc)
  sigma_asym = 0.10 v_obs (dwarfs) or 0.05 v_obs (spirals)
  sigma_turb = k_turb * v_obs * (1 - exp(-r/R_d))^p_turb, k_turb=0.07, p_turb=1.3

Inner-beam mask r >= b_kpc; if no beam available, set b_kpc = 0.3 * R_d.

Inputs:
  - master table pickle with fields per galaxy:
      r[kpc], v_obs, v_gas, v_disk, v_bul, R_d, f_gas_proxy
    Default path tries 'active/results/sparc_master.pkl', then 'sparc_master.pkl'.

Outputs:
  - CSV per-galaxy with reduced chi^2 and summary statistics to stdout
"""

from __future__ import annotations

import argparse
import os
import pickle
from pathlib import Path
from typing import Dict, Any, Tuple

import numpy as np
import pandas as pd


def phi() -> float:
    return (1.0 + np.sqrt(5.0)) / 2.0


PHI = phi()
ALPHA = 0.5 * (1.0 - 1.0 / PHI)
C_LAG = PHI ** (-5.0)
A0 = 1.2e-10  # m s^-2

# n(r) parameters (kpc)
N_A = 7.0
N_R0_KPC = 8.0
N_P = 1.6

# error model
SIGMA0 = 10.0  # km/s
F_FRAC = 0.05
ALPHA_BEAM = 0.3
K_TURB = 0.07
P_TURB = 1.3

# classification threshold for dwarfs (km/s)
V_DWARF_MAX = 80.0


def load_master_table(path: Path) -> Dict[str, Dict[str, Any]]:
    with open(path, "rb") as f:
        return pickle.load(f)


def get_master_path() -> Path:
    candidates = [
        Path("active/results/sparc_master.pkl"),
        Path("sparc_master.pkl"),
        Path("galaxy-rotation/results/ledger_final_combined_results.pkl")  # fallback, may not match schema
    ]
    for p in candidates:
        if p.exists():
            return p
    raise FileNotFoundError("No master table pickle found. Looked for: " + ", ".join(map(str, candidates)))


def baryonic_speed(v_gas: np.ndarray, v_disk: np.ndarray, v_bul: np.ndarray, upsilon_star: float = 1.0) -> np.ndarray:
    # Single global M/L enters as sqrt(upsilon) on disk term
    return np.sqrt(np.maximum(0.0, v_gas ** 2 + (np.sqrt(upsilon_star) * v_disk) ** 2 + v_bul ** 2))


def g_bar_ms2(v_bar_kms: np.ndarray, r_kpc: np.ndarray) -> np.ndarray:
    # g_bar = v^2 / r with unit conversions: v in km/s, r in kpc
    v2_m2s2 = (v_bar_kms ** 2) * (1000.0 ** 2)
    r_m = r_kpc * 3.086e19
    # Avoid divide-by-zero
    r_m = np.where(r_m > 0.0, r_m, np.nan)
    return v2_m2s2 / r_m


def n_of_r(r_kpc: np.ndarray) -> np.ndarray:
    x = np.maximum(0.0, r_kpc) / N_R0_KPC
    return 1.0 + N_A * (1.0 - np.exp(-(x ** N_P)))


def zeta_of_r(r_kpc: np.ndarray, h_over_Rd: float = 0.25) -> np.ndarray:
    # Geometry correction placeholder: default unity, clip bounds [0.8, 1.2]
    z = np.ones_like(r_kpc)
    return np.clip(z, 0.8, 1.2)


def xi_from_quintile(u_center: float) -> float:
    # ξ = 1 + φ^{-5} * u_b^{1/2}, u_b is bin center in (0,1)
    return 1.0 + C_LAG * np.sqrt(max(0.0, min(1.0, u_center)))


def threads_bins_from_f_gas_proxy(values: np.ndarray, B: int = 5) -> Tuple[np.ndarray, np.ndarray]:
    """Compute global quantile thresholds and assign each value a bin center u_b=(b+0.5)/B."""
    # thresholds at quantiles 1/B, 2/B, ..., (B-1)/B
    qs = [np.nanquantile(values, q) for q in [i / B for i in range(1, B)]]
    thresholds = np.array(qs, dtype=float)
    # assign bins
    bins = np.digitize(values, thresholds, right=False)
    u_centers = (bins + 0.5) / B
    return bins, u_centers


def w_total(r_kpc: np.ndarray, v_bar_kms: np.ndarray, xi: float, g_ext: float = 0.0) -> np.ndarray:
    r_kpc = np.asarray(r_kpc, dtype=float)
    v_bar_kms = np.asarray(v_bar_kms, dtype=float)
    n_r = n_of_r(r_kpc)
    zeta_r = zeta_of_r(r_kpc)
    gbar = g_bar_ms2(v_bar_kms, r_kpc)
    # 1 + C_lag [ ((g_bar+g_ext)/a0)^(-alpha) - (1+g_ext/a0)^(-alpha) ]
    # handle NaNs safely
    base = np.power(np.maximum(1e-300, (gbar + g_ext) / A0), -ALPHA) - np.power(1.0 + g_ext / A0, -ALPHA)
    core = 1.0 + C_LAG * base
    w = xi * n_r * zeta_r * core
    return np.where(np.isfinite(w), np.maximum(w, 1e-6), 1.0)


def sigma_eff_kms(
    r_kpc: np.ndarray,
    v_obs_kms: np.ndarray,
    R_d_kpc: float,
    dwarf: bool,
    b_kpc: float | None = None,
) -> np.ndarray:
    r = np.asarray(r_kpc, dtype=float)
    v = np.asarray(v_obs_kms, dtype=float)
    sigma_obs = np.zeros_like(v)  # if observational errors not available per point; set to 0
    sigma0 = SIGMA0
    f = F_FRAC
    alpha_beam = ALPHA_BEAM
    # beam proxy
    if b_kpc is None:
        b_kpc = 0.3 * max(R_d_kpc, 1e-6)
    sigma_beam = alpha_beam * b_kpc * v / (r + b_kpc)
    sigma_asym = (0.10 if dwarf else 0.05) * v
    sigma_turb = K_TURB * v * np.power(1.0 - np.exp(-r / max(R_d_kpc, 1e-6)), P_TURB)
    # quadrature
    sig2 = (
        sigma_obs ** 2
        + sigma0 ** 2
        + (f * v) ** 2
        + sigma_beam ** 2
        + sigma_asym ** 2
        + sigma_turb ** 2
    )
    return np.sqrt(np.maximum(sig2, 1e-12))


def reduced_chi2(
    v_obs: np.ndarray,
    v_model: np.ndarray,
    sigma_eff: np.ndarray,
    r_kpc: np.ndarray,
    b_kpc: float,
) -> Tuple[float, int]:
    mask = r_kpc >= b_kpc
    v_o = v_obs[mask]
    v_m = v_model[mask]
    s = sigma_eff[mask]
    N = int(np.sum(mask))
    if N <= 1:
        return np.nan, 0
    chi2 = np.sum(((v_o - v_m) / s) ** 2)
    return float(chi2 / N), N


def main():
    ap = argparse.ArgumentParser(description="ILG rotation benchmark (global-only)")
    ap.add_argument("--master", type=str, default=None, help="Path to master table pickle")
    ap.add_argument("--ml_disk", type=float, default=1.0, help="Global stellar M/L (default 1.0)")
    ap.add_argument("--bins", type=int, default=5, help="Number of global bins for xi (default 5)")
    ap.add_argument("--out", type=str, default="results/ilg_rotation_benchmark.csv", help="Output CSV path")
    args = ap.parse_args()

    # Load master table
    if args.master is None:
        path = get_master_path()
    else:
        path = Path(args.master)
    master = load_master_table(path)

    # Prepare xi via global quintiles of f_gas_proxy (fallback to zeros if missing)
    f_gas_list = []
    keys = list(master.keys())
    for name in keys:
        g = master[name]
        f_proxy = g.get("f_gas_true", g.get("f_gas_proxy", np.nan))
        f_gas_list.append(f_proxy)
    f_gas_array = np.array(f_gas_list, dtype=float)
    # sanitize
    f_gas_array = np.where(np.isfinite(f_gas_array), f_gas_array, np.nan)

    bins, u_centers = threads_bins_from_f_gas_proxy(np.nan_to_num(f_gas_array, nan=np.nanmedian(f_gas_array)), B=args.bins)

    # Global summary rows
    rows = []
    chi2_list = []

    for i, name in enumerate(keys):
        g = master[name]
        df = g.get("data")
        if df is None:
            # Some master tables store arrays directly
            r = np.asarray(g["r"], dtype=float)
            v_obs = np.asarray(g["v_obs"], dtype=float)
            v_gas = np.asarray(g["v_gas"], dtype=float) if "v_gas" in g else np.zeros_like(r)
            v_disk = np.asarray(g["v_disk"], dtype=float) if "v_disk" in g else np.zeros_like(r)
            v_bul = np.asarray(g["v_bul"], dtype=float) if "v_bul" in g else np.zeros_like(r)
        else:
            r = df["rad"].to_numpy(float)
            v_obs = df["vobs"].to_numpy(float)
            v_gas = df["vgas"].to_numpy(float)
            v_disk = df["vdisk"].to_numpy(float)
            v_bul = df["vbul"].to_numpy(float)

        # basic sanity filter
        ok = (r > 0) & (v_obs > 0)
        r = r[ok]
        v_obs = v_obs[ok]
        v_gas = v_gas[ok]
        v_disk = v_disk[ok]
        v_bul = v_bul[ok]
        if r.size < 3:
            continue

        R_d = float(g.get("R_d", 2.0))
        b_kpc = 0.3 * max(R_d, 1e-6)

        v_bar = baryonic_speed(v_gas, v_disk, v_bul, upsilon_star=args.ml_disk)
        xi_u = float(u_centers[i]) if i < len(u_centers) else 0.5
        xi = xi_from_quintile(xi_u)

        w_tot = w_total(r, v_bar, xi=xi, g_ext=0.0)
        v_model = np.sqrt(np.maximum(1e-12, w_tot)) * v_bar

        # classify dwarf vs spiral by outer observed speed
        v_outer = np.nanmedian(v_obs[-3:]) if v_obs.size >= 3 else np.nanmax(v_obs)
        dwarf = bool(v_outer < V_DWARF_MAX)

        sigma_eff = sigma_eff_kms(r, v_obs, R_d_kpc=R_d, dwarf=dwarf, b_kpc=b_kpc)
        red_chi2, N = reduced_chi2(v_obs, v_model, sigma_eff, r, b_kpc)

        if np.isfinite(red_chi2) and N > 0:
            chi2_list.append(red_chi2)
            rows.append({
                "galaxy": name,
                "N": N,
                "chi2_over_N": red_chi2
            })

    if not rows:
        print("No galaxies evaluated.")
        return

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    pd.DataFrame(rows).to_csv(out_path, index=False)

    chi2_arr = np.array(chi2_list, dtype=float)
    print(f"Evaluated {chi2_arr.size} galaxies")
    print(f"Median chi^2/N = {np.nanmedian(chi2_arr):.3f}")
    print(f"Mean   chi^2/N = {np.nanmean(chi2_arr):.3f}")
    print(f"Results written to {out_path}")


if __name__ == "__main__":
    main()


