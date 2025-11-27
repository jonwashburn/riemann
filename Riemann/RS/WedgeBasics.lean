import Riemann.Cert.KxiPPlus
import Riemann.RS.PoissonKernelDyadic

/-
Small, self-contained helpers for the boundary wedge development.
We provide WhitneyInterval-flavored wrappers around the dyadic separation
lemmas already available in PoissonKernelDyadic.
-/

noncomputable section
open Real

namespace RH
namespace RS
namespace WedgeBasics

open RH.Cert
open RH.RS.PoissonKernelDyadic

/-- Wrapper: separation from the base interval stated with `WhitneyInterval`.
If `γ` lies in the k‑th annulus w.r.t. center `I.t0` and scale `I.len`, and `k ≥ 1`,
then for all `t ∈ I.interval` one has `|t − γ| ≥ 2^{k−1} · I.len`. -/
lemma sep_from_base_of_annulus_Whitney
    (I : RH.Cert.WhitneyInterval) {k : ℕ} (hk : 1 ≤ k) {γ : ℝ}
    (hAnn : RH.RS.PoissonKernelDyadic.inDyadicAnnulus I.t0 I.len k γ) :
    ∀ t ∈ I.interval, (2 : ℝ) ^ (k - 1) * I.len ≤ |t - γ| := by
  intro t ht
  -- `|t - I.t0| ≤ I.len` for `t ∈ I.interval`
  have hbase : |t - I.t0| ≤ I.len := by
    -- `I.interval = Icc (t0 - len) (t0 + len)`
    have hmem : t ∈ Set.Icc (I.t0 - I.len) (I.t0 + I.len) := by
      simpa [RH.Cert.WhitneyInterval.interval] using ht
    have h1 : I.t0 - I.len ≤ t := hmem.1
    have h2 : t ≤ I.t0 + I.len := hmem.2
    have hlen : 0 ≤ I.len := I.len_pos.le
    have hleft : -I.len ≤ t - I.t0 := by linarith
    have hright : t - I.t0 ≤ I.len := by linarith
    exact (abs_le.mpr ⟨hleft, hright⟩)
  -- apply the dyadic separation lemma
  exact RH.RS.PoissonKernelDyadic.sep_from_base_of_annulus
    (c := I.t0) (L := I.len) (t := t) (x := γ) (k := k)
    hbase hAnn hk

/-- Wrapper: when two points live in distinct annuli whose indices differ by at least two,
their separation is controlled uniformly in terms of the annulus size. -/
lemma sep_between_annuli_gap_ge_two_Whitney
    (I : RH.Cert.WhitneyInterval) {k j : ℕ} {x y : ℝ}
    (hAnnX : RH.RS.PoissonKernelDyadic.inDyadicAnnulus I.t0 I.len k x)
    (hAnnY : RH.RS.PoissonKernelDyadic.inDyadicAnnulus I.t0 I.len j y)
    (hgap : 2 ≤ Nat.dist k j) :
    (1 / 2 : ℝ) * (2 : ℝ) ^ (Nat.dist k j) * I.len ≤ |x - y| :=
  RH.RS.PoissonKernelDyadic.sep_between_annuli_gap_ge_two
    (c := I.t0) (L := I.len) (x := x) (y := y) (k := k) (j := j)
    hAnnX hAnnY I.len_pos hgap

end WedgeBasics
end RS
end RH
