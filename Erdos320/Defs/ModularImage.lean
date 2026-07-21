import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Modular subset-sum images `Σ_p(m)` and their sizes `σ_p(m)`

The manuscript's eq. `sigma-def`: for a prime `p` and `m < p`,
```
Σ_p(m) = { ∑_{k=1}^m ε_k · k⁻¹ (mod p) : ε_k ∈ {0,1} } ⊆ 𝔽_p,
σ_p(m) = |Σ_p(m)|,
```
the set of subset sums of the inverses `1⁻¹, …, m⁻¹` in `𝔽_p`.

We define it for all `p, m : ℕ` via `ZMod p` (for non-prime or small `p` the
definition is still meaningful, just not used by the paper).  The inverse in
`ZMod p` is Mathlib's, which is the field inverse for prime `p`.
-/

namespace Erdos320

open Finset

/-- `modularImage p m` is the manuscript's `Σ_p(m)` (eq. `sigma-def`): the set
of subset sums of `{1⁻¹, …, m⁻¹}` in `ZMod p`. -/
def modularImage (p m : ℕ) : Finset (ZMod p) :=
  (Icc 1 m).powerset.image fun A : Finset ℕ => ∑ k ∈ A, (k : ZMod p)⁻¹

/-- `sigma p m` is the manuscript's `σ_p(m) = |Σ_p(m)|` (eq. `sigma-def`). -/
def sigma (p m : ℕ) : ℕ := (modularImage p m).card

theorem zero_mem_modularImage (p m : ℕ) : (0 : ZMod p) ∈ modularImage p m := by
  have h : (∅ : Finset ℕ) ∈ (Icc 1 m).powerset := empty_mem_powerset _
  have h2 := mem_image_of_mem (fun A : Finset ℕ => ∑ k ∈ A, (k : ZMod p)⁻¹) h
  simpa [modularImage] using h2

theorem modularImage_nonempty (p m : ℕ) : (modularImage p m).Nonempty :=
  ⟨0, zero_mem_modularImage p m⟩

theorem one_le_sigma (p m : ℕ) : 1 ≤ sigma p m :=
  card_pos.mpr (modularImage_nonempty p m)

/-- Trivial cardinality bound: `Σ_p(m) ⊆ ZMod p`, so `σ_p(m) ≤ p`
(for `p > 0`). -/
theorem sigma_le_self {p : ℕ} (hp : 0 < p) (m : ℕ) : sigma p m ≤ p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  have h : (modularImage p m).card ≤ Fintype.card (ZMod p) := card_le_univ _
  rwa [ZMod.card p] at h

end Erdos320
