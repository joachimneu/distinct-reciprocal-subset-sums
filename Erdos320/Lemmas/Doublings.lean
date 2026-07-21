import Erdos320.Lemmas.SBasic
import Erdos320.Defs.ModularImage
import Erdos320.Defs.RatToZMod
import Erdos320.Assumptions
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# The Bettin–Grenié–Molteni–Sanna doubling identities `S n = 2·S(n−1)`

This file mechanizes the "doubling" step of the manuscript's high finite input
(§8, feeding `comp:high`): for the `35` certified indices
`n ∈ {86, …, 151}` the counting function *exactly* doubles,
```
S(n) = 2·S(n−1),
```
and, chaining these with monotonicity from the exact table `S(0), …, S(83)`
(`bgmsSTable`), one obtains the certified lower bounds `S(m) ≥ sLowerBGMS m`
for all `m ≤ 154`.

## The mathematics being checked

`S(n+1) ≤ 2·S(n)` always holds (`S_succ_le_two_mul`), because
`𝓔_{n} = 𝓔_{n-1} ∪ (𝓔_{n-1} + 1/n)`.  Equality — the doubling — holds exactly
when the two halves are **disjoint**: no `x, y ∈ 𝓔_{n-1}` satisfy
`x = y + 1/n`.  BGMS prove disjointness by a mod-`p` argument.  Write
`n = p^a · k` for a prime `p` with `p ∤ k` and, crucially, `k < p`.  A putative
equality `∑_{j∈A} 1/j = 1/n + ∑_{j∈B} 1/j` (with `A, B ⊆ {1,…,n-1}`) is mapped
into `ZMod p` by `x ↦ p^a·x (mod p)` (here `coordPow p a`).  The bound `k < p`
forces every `j ≤ n-1` to have `p`-adic valuation `≤ a`; the terms with
valuation `< a` are annihilated by the factor `p^a`, and a term `j = p^a·ℓ`
(with `p ∤ ℓ`, `1 ≤ ℓ ≤ k-1`) contributes `ℓ⁻¹`.  Hence the image of `𝓔_{n-1}`
lands in `Σ_p(k-1) = modularImage p (k-1)`, and `1/n` maps to `k⁻¹`, so the
equality would put `k⁻¹` into the difference set
`Σ_p(k-1) − Σ_p(k-1)`.  The finite check
`Disjoint (Σ_p(k-1)) (Σ_p(k-1) + k⁻¹)` (discharged by `native_decide` over the
concrete `ZMod p`, `p < 160`) therefore rules the equality out — and gives
disjointness, hence the doubling.

Note `a = 1` is **not** uniform: four witnesses use a genuine prime power
(`98 = 7²·2`, `121 = 11²`, `125 = 5³`, `128 = 2⁷`), so `disjoint_of_modCheck`
is proved for general `a` via the `p`-adic valuation bookkeeping
(`Nat.ordProj`/`Nat.ordCompl`).

Everything here is genuinely proved: the only axioms reached are `bgmsSTable`
(the exact table, an `Assumptions.lean` input) and — from `native_decide` on the
finite `ZMod p` checks — `Lean.ofReduceBool`.
-/

namespace Erdos320

open Finset

/-! ## Part 1 — the doubling from disjointness -/

/-- **The doubling from disjointness.**  If the two halves
`𝓔_{n-1}` and `𝓔_{n-1} + 1/n` of `𝓔_n` are disjoint, then `S n = 2·S(n-1)`.
The decomposition `𝓔_n = 𝓔_{n-1} ∪ (𝓔_{n-1} + 1/n)` upgrades the `⊆` of
`S_succ_le_two_mul` to an equality; disjointness makes the union's cardinality
additive, and the shift `x ↦ x + 1/n` is injective. -/
theorem S_two_mul_of_disjoint {n : ℕ} (hn : 1 ≤ n)
    (hdisj : Disjoint (reciprocalSubsetSumSet (n - 1))
              ((reciprocalSubsetSumSet (n - 1)).image (fun x => x + (1 : ℚ) / (n : ℚ)))) :
    S n = 2 * S (n - 1) := by
  have hset : reciprocalSubsetSumSet n
      = reciprocalSubsetSumSet (n - 1)
        ∪ (reciprocalSubsetSumSet (n - 1)).image (fun x => x + (1 : ℚ) / (n : ℚ)) := by
    apply Finset.Subset.antisymm
    · intro y hy
      simp only [reciprocalSubsetSumSet, Finset.mem_image, Finset.mem_powerset] at hy
      obtain ⟨A, hA, rfl⟩ := hy
      by_cases hmem : n ∈ A
      · apply Finset.mem_union_right
        rw [Finset.mem_image]
        refine ⟨∑ i ∈ A.erase n, (1 : ℚ) / (i : ℚ), ?_, ?_⟩
        · simp only [reciprocalSubsetSumSet, Finset.mem_image, Finset.mem_powerset]
          refine ⟨A.erase n, ?_, rfl⟩
          intro a ha
          have haA := hA (Finset.mem_of_mem_erase ha)
          have hane := Finset.ne_of_mem_erase ha
          rw [Finset.mem_Icc] at haA ⊢
          omega
        · show (∑ i ∈ A.erase n, (1 : ℚ) / (i : ℚ)) + (1 : ℚ) / (n : ℚ)
              = ∑ i ∈ A, (1 : ℚ) / (i : ℚ)
          exact Finset.sum_erase_add A (fun i => (1 : ℚ) / (i : ℚ)) hmem
      · apply Finset.mem_union_left
        simp only [reciprocalSubsetSumSet, Finset.mem_image, Finset.mem_powerset]
        refine ⟨A, ?_, rfl⟩
        intro a ha
        have haA := hA ha
        have hane : a ≠ n := fun h => hmem (h ▸ ha)
        rw [Finset.mem_Icc] at haA ⊢
        omega
    · apply Finset.union_subset
      · exact reciprocalSubsetSumSet_subset_of_le (by omega)
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simp only [reciprocalSubsetSumSet, Finset.mem_image, Finset.mem_powerset] at hx ⊢
        obtain ⟨A, hA, rfl⟩ := hx
        have hnA : n ∉ A := by
          intro h
          have := hA h
          rw [Finset.mem_Icc] at this
          omega
        refine ⟨insert n A, ?_, ?_⟩
        · intro a ha
          rw [Finset.mem_insert] at ha
          rcases ha with rfl | ha
          · rw [Finset.mem_Icc]; omega
          · have haA := hA ha
            rw [Finset.mem_Icc] at haA ⊢
            omega
        · rw [Finset.sum_insert hnA]
          ring
  simp only [S]
  rw [hset, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (add_left_injective ((1 : ℚ) / (n : ℚ)))]
  ring

/-! ## Part 2 — the disjointness criterion via a finite `ZMod p` check -/

/-- The generalized coordinate map `x ↦ p^a·x (mod p)`, the BGMS reduction used
to certify disjointness for `n = p^a·k`.  (For `a = 1` this is `coord p` of
`LargePrimeDecomposition`.) -/
def coordPow (p a : ℕ) (x : ℚ) : ZMod p := ratToZMod p ((p : ℚ) ^ a * x)

/-- Every denominator `j ≤ p^a·k − 1` has `p`-adic valuation at most `a`,
because `k < p` gives `p^a·k < p^{a+1}`. -/
theorem mem_fact_le {p : ℕ} (hp : p.Prime) {a k : ℕ} (hk : 1 ≤ k) (hkp : k < p)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ p ^ a * k - 1) : j.factorization p ≤ a := by
  have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
  have hnpos : 0 < p ^ a * k := mul_pos hpa_pos hk
  have hn_lt : p ^ a * k < p ^ (a + 1) := by
    rw [pow_succ]; exact mul_lt_mul_of_pos_left hkp hpa_pos
  have hjlt : j < p ^ (a + 1) := by omega
  by_contra hcon
  push Not at hcon
  have hdvd : p ^ (a + 1) ∣ j := (hp.pow_dvd_iff_le_factorization (by omega)).mpr (by omega)
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **Per-term computation of the reduction.**  For `1 ≤ j` with
`v_p(j) ≤ a`, the scaled reciprocal `p^a·(1/j)` has a `p`-coprime denominator,
and its reduction is `p^{a−v_p(j)}·(ordCompl_p j)⁻¹` in `ZMod p` — which is `0`
when `v_p(j) < a` (the factor `p` annihilates it) and `(ordCompl_p j)⁻¹` when
`v_p(j) = a`. -/
theorem coordPow_recip {p : ℕ} (hp : p.Prime) {a j : ℕ} (hj : 1 ≤ j)
    (hv : j.factorization p ≤ a) :
    (¬ p ∣ ((p : ℚ) ^ a * ((1 : ℚ) / (j : ℚ))).den) ∧
      ratToZMod p ((p : ℚ) ^ a * ((1 : ℚ) / (j : ℚ)))
        = (p : ZMod p) ^ (a - j.factorization p) * ((ordCompl[p] j : ℕ) : ZMod p)⁻¹ := by
  have hj0 : j ≠ 0 := by omega
  have hpℚ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hpvℚ : (p : ℚ) ^ (j.factorization p) ≠ 0 := pow_ne_zero _ hpℚ
  have hq0 : ((ordCompl[p] j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ordCompl_pos p hj0).ne'
  have hfacℚ : (p : ℚ) ^ (j.factorization p) * ((ordCompl[p] j : ℕ) : ℚ) = (j : ℚ) := by
    exact_mod_cast Nat.ordProj_mul_ordCompl_eq_self j p
  have key : (p : ℚ) ^ a * ((1 : ℚ) / (j : ℚ)) * ((ordCompl[p] j : ℕ) : ℚ)
      = (p : ℚ) ^ (a - j.factorization p) := by
    have h1 : (p : ℚ) ^ a
        = (p : ℚ) ^ (a - j.factorization p) * (p : ℚ) ^ (j.factorization p) := by
      rw [← pow_add, Nat.sub_add_cancel hv]
    rw [h1, ← hfacℚ]
    field_simp
  have hbℤ : ¬ (p : ℤ) ∣ ((ordCompl[p] j : ℕ) : ℤ) := by
    rw [Int.natCast_dvd_natCast]; exact Nat.not_dvd_ordCompl hp hj0
  have habℚ : ((p : ℚ) ^ a * ((1 : ℚ) / (j : ℚ))) * (((ordCompl[p] j : ℕ) : ℤ) : ℚ)
      = (((p ^ (a - j.factorization p) : ℕ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Int.cast_natCast, Nat.cast_pow]
    exact key
  refine ⟨not_dvd_den_of_mul_intCast_eq hp hbℤ habℚ, ?_⟩
  rw [ratToZMod_unique hp hbℤ habℚ, Int.cast_natCast, Int.cast_natCast, Nat.cast_pow]

/-- The image of `𝓔_{p^a·k−1}` under `coordPow p a` lands in the modular image
`Σ_p(k−1)`.  This is the core reduction: the `p`-adic bookkeeping picks out the
`j = p^a·ℓ` terms, whose `ℓ`'s range over a subset of `{1,…,k-1}`. -/
theorem coordPow_mem_modularImage {p : ℕ} (hp : p.Prime) {a k : ℕ} (hk : 1 ≤ k) (hkp : k < p)
    {x : ℚ} (hx : x ∈ reciprocalSubsetSumSet (p ^ a * k - 1)) :
    coordPow p a x ∈ modularImage p (k - 1) := by
  have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
  have hnpos : 0 < p ^ a * k := mul_pos hpa_pos hk
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
  have hAsub : A ⊆ Icc 1 (p ^ a * k - 1) := Finset.mem_powerset.mp hA
  have hfle : ∀ j ∈ A, j.factorization p ≤ a := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp (hAsub hj)
    exact mem_fact_le hp hk hkp hj1 hj2
  have hden : ∀ j ∈ A, ¬ p ∣ ((p : ℚ) ^ a * ((1 : ℚ) / (j : ℚ))).den := by
    intro j hj
    obtain ⟨hj1, _⟩ := Finset.mem_Icc.mp (hAsub hj)
    exact (coordPow_recip hp hj1 (hfle j hj)).1
  have hterm : ∀ j ∈ A, ratToZMod p ((p : ℚ) ^ a * ((1 : ℚ) / (j : ℚ)))
      = if p ^ a ∣ j then ((ordCompl[p] j : ℕ) : ZMod p)⁻¹ else 0 := by
    intro j hj
    obtain ⟨hj1, _⟩ := Finset.mem_Icc.mp (hAsub hj)
    rw [(coordPow_recip hp hj1 (hfle j hj)).2]
    by_cases hd : p ^ a ∣ j
    · rw [if_pos hd]
      have hge : a ≤ j.factorization p := (hp.pow_dvd_iff_le_factorization (by omega)).mp hd
      have hva : j.factorization p = a := le_antisymm (hfle j hj) hge
      rw [hva, Nat.sub_self, pow_zero, one_mul]
    · rw [if_neg hd]
      have hlt : j.factorization p < a := by
        rcases lt_or_ge (j.factorization p) a with h | h
        · exact h
        · exact absurd ((hp.pow_dvd_iff_le_factorization (by omega)).mpr h) hd
      rw [ZMod.natCast_self, zero_pow (by omega), zero_mul]
  have hinj : ∀ j₁ ∈ A.filter (fun j => p ^ a ∣ j), ∀ j₂ ∈ A.filter (fun j => p ^ a ∣ j),
      ordCompl[p] j₁ = ordCompl[p] j₂ → j₁ = j₂ := by
    intro j₁ h₁ j₂ h₂ heq
    obtain ⟨hj₁A, hd₁⟩ := Finset.mem_filter.mp h₁
    obtain ⟨hj₂A, hd₂⟩ := Finset.mem_filter.mp h₂
    obtain ⟨hj₁1, _⟩ := Finset.mem_Icc.mp (hAsub hj₁A)
    obtain ⟨hj₂1, _⟩ := Finset.mem_Icc.mp (hAsub hj₂A)
    have hv₁ : j₁.factorization p = a :=
      le_antisymm (hfle j₁ hj₁A) ((hp.pow_dvd_iff_le_factorization (by omega)).mp hd₁)
    have hv₂ : j₂.factorization p = a :=
      le_antisymm (hfle j₂ hj₂A) ((hp.pow_dvd_iff_le_factorization (by omega)).mp hd₂)
    have hproj₁ : ordProj[p] j₁ = p ^ a := by rw [hv₁]
    have hproj₂ : ordProj[p] j₂ = p ^ a := by rw [hv₂]
    have e₁ : p ^ a * ordCompl[p] j₁ = j₁ := by
      rw [← hproj₁]; exact Nat.ordProj_mul_ordCompl_eq_self j₁ p
    have e₂ : p ^ a * ordCompl[p] j₂ = j₂ := by
      rw [← hproj₂]; exact Nat.ordProj_mul_ordCompl_eq_self j₂ p
    rw [← e₁, ← e₂, heq]
  show ratToZMod p ((p : ℚ) ^ a * ∑ n ∈ A, (1 : ℚ) / (n : ℚ)) ∈ modularImage p (k - 1)
  rw [Finset.mul_sum, ratToZMod_sum hp hden, Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  apply Finset.mem_image.mpr
  refine ⟨(A.filter (fun j => p ^ a ∣ j)).image (fun j => ordCompl[p] j),
    Finset.mem_powerset.mpr ?_, Finset.sum_image hinj⟩
  intro l hl
  obtain ⟨j, hjf, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨hjA, hd⟩ := Finset.mem_filter.mp hjf
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp (hAsub hjA)
  have hv : j.factorization p = a :=
    le_antisymm (hfle j hjA) ((hp.pow_dvd_iff_le_factorization (by omega)).mp hd)
  have hproj : ordProj[p] j = p ^ a := by rw [hv]
  have ecompl : p ^ a * ordCompl[p] j = j := by
    rw [← hproj]; exact Nat.ordProj_mul_ordCompl_eq_self j p
  rw [Finset.mem_Icc]
  refine ⟨Nat.ordCompl_pos p (by omega), ?_⟩
  have hmul : p ^ a * ordCompl[p] j < p ^ a * k := by rw [ecompl]; omega
  have hlk : ordCompl[p] j < k := lt_of_mul_lt_mul_left hmul (Nat.zero_le _)
  omega

/-- The scaled reduction of `1/n` for `n = p^a·k` (with `p ∤ k`, `k < p`) is
`k⁻¹`: after scaling, `p^a·(1/n) = 1/k`. -/
theorem ratToZMod_target {p : ℕ} (hp : p.Prime) {a k : ℕ} (hk : 1 ≤ k) (hkp : k < p) :
    ratToZMod p ((p : ℚ) ^ a * ((1 : ℚ) / ((p ^ a * k : ℕ) : ℚ))) = (k : ZMod p)⁻¹ := by
  have hpk : ¬ p ∣ k := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hbℤ : ¬ (p : ℤ) ∣ ((k : ℕ) : ℤ) := by rw [Int.natCast_dvd_natCast]; exact hpk
  have hpℚ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hkℚ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((p ^ a * k : ℕ) : ℚ) = (p : ℚ) ^ a * (k : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
  have hab : ((p : ℚ) ^ a * ((1 : ℚ) / ((p ^ a * k : ℕ) : ℚ))) * (((k : ℕ) : ℤ) : ℚ)
      = ((1 : ℤ) : ℚ) := by
    rw [hcast]
    push_cast
    rw [mul_one_div, div_mul_eq_mul_div, div_self (mul_ne_zero (pow_ne_zero a hpℚ) hkℚ)]
  rw [ratToZMod_unique hp hbℤ hab]
  simp

/-- The denominator of `p^a·x` is coprime to `p` for any `x ∈ 𝓔_{p^a·k−1}`. -/
theorem coordPow_arg_den {p : ℕ} (hp : p.Prime) {a k : ℕ} (hk : 1 ≤ k) (hkp : k < p)
    {x : ℚ} (hx : x ∈ reciprocalSubsetSumSet (p ^ a * k - 1)) :
    ¬ p ∣ ((p : ℚ) ^ a * x).den := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hx
  have hAsub : A ⊆ Icc 1 (p ^ a * k - 1) := Finset.mem_powerset.mp hA
  rw [Finset.mul_sum]
  apply not_dvd_den_sum hp
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp (hAsub hj)
  exact (coordPow_recip hp hj1 (mem_fact_le hp hk hkp hj1 hj2)).1

/-- **The disjointness criterion (BGMS mod-`p`).**  If the finite `ZMod p`
check passes — `Σ_p(k−1)` is disjoint from its shift by `k⁻¹` — then the two
halves of `𝓔_{p^a·k}` are disjoint. -/
theorem disjoint_of_modCheck {p a k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    (hcheck : Disjoint (modularImage p (k - 1))
                ((modularImage p (k - 1)).image (fun x => x + (k : ZMod p)⁻¹))) :
    Disjoint (reciprocalSubsetSumSet (p ^ a * k - 1))
             ((reciprocalSubsetSumSet (p ^ a * k - 1)).image
                (fun x => x + (1 : ℚ) / ((p ^ a * k : ℕ) : ℚ))) := by
  have hpℚ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hkℚ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbℤ : ¬ (p : ℤ) ∣ ((k : ℕ) : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    exact fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
  have hcast : ((p ^ a * k : ℕ) : ℚ) = (p : ℚ) ^ a * (k : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
  have hsimp : (p : ℚ) ^ a * ((1 : ℚ) / ((p ^ a * k : ℕ) : ℚ)) = (1 : ℚ) / (k : ℚ) := by
    rw [hcast, mul_one_div, ← div_div, div_self (pow_ne_zero a hpℚ)]
  rw [Finset.disjoint_left]
  intro z hz hz2
  obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hz2
  have hzmem := coordPow_mem_modularImage hp hk hkp hz
  have hwmem := coordPow_mem_modularImage hp hk hkp hw
  have hd1 : ¬ p ∣ ((p : ℚ) ^ a * w).den := coordPow_arg_den hp hk hkp hw
  have hd2 : ¬ p ∣ ((p : ℚ) ^ a * ((1 : ℚ) / ((p ^ a * k : ℕ) : ℚ))).den := by
    rw [hsimp]
    refine not_dvd_den_of_mul_intCast_eq hp (a := (1 : ℤ)) (b := ((k : ℕ) : ℤ)) hbℤ ?_
    push_cast
    rw [one_div, inv_mul_cancel₀ hkℚ]
  have hval : coordPow p a z = coordPow p a w + (k : ZMod p)⁻¹ := by
    have hz_eq : z = w + (1 : ℚ) / ((p ^ a * k : ℕ) : ℚ) := hwz.symm
    show ratToZMod p ((p : ℚ) ^ a * z)
        = ratToZMod p ((p : ℚ) ^ a * w) + (k : ZMod p)⁻¹
    rw [hz_eq, mul_add, ratToZMod_add hp hd1 hd2, ratToZMod_target hp hk hkp]
  rw [Finset.disjoint_left] at hcheck
  exact hcheck hzmem (Finset.mem_image.mpr ⟨coordPow p a w, hwmem, hval.symm⟩)

/-- Package Parts 1 and 2: given a witness `n = p^a·k` passing the finite check,
`S n = 2·S(n-1)`. -/
theorem S_two_mul_of_modCheck {n p a k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    (hn : n = p ^ a * k)
    (hcheck : Disjoint (modularImage p (k - 1))
                ((modularImage p (k - 1)).image (fun x => x + (k : ZMod p)⁻¹))) :
    S n = 2 * S (n - 1) := by
  have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
  have h1 : 1 ≤ n := by rw [hn]; exact mul_pos hpa_pos hk
  have hdisj : Disjoint (reciprocalSubsetSumSet (n - 1))
      ((reciprocalSubsetSumSet (n - 1)).image (fun x => x + (1 : ℚ) / (n : ℚ))) := by
    rw [hn]
    exact disjoint_of_modCheck hp hk hkp hcheck
  exact S_two_mul_of_disjoint h1 hdisj

/-! ## Part 3 — the 35 witnesses, the ledger, and the lower bounds -/

/-- The `35` certified doubling indices (in increasing order), from
`doubling_witness` in `directed_interval_certificate.py`. -/
def doublingIndices : List ℕ :=
  [86, 87, 89, 92, 93, 94, 97, 98, 101, 103, 106, 107, 109, 111, 113, 116, 118,
   121, 122, 123, 124, 125, 127, 128, 129, 131, 134, 137, 139, 141, 142, 146,
   148, 149, 151]

/-- **The 35 doubling identities.**  `S d = 2·S(d-1)` for every certified index
`d`.  Each is discharged by the mod-`p` criterion with its witness prime; the
finite `ZMod p` check is a `native_decide`. -/
theorem doubling_holds : ∀ d ∈ doublingIndices, S d = 2 * S (d - 1) := by
  intro d hd
  fin_cases hd
  · exact S_two_mul_of_modCheck (p := 43) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 29) (a := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 89) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 23) (a := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 31) (a := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 47) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 97) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 7) (a := 2) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 101) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 103) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 53) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 107) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 109) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 37) (a := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 113) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 29) (a := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 59) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 11) (a := 2) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 61) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 41) (a := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 31) (a := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 5) (a := 3) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 127) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 2) (a := 7) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 43) (a := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 131) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 67) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 137) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 139) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 47) (a := 1) (k := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 71) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 73) (a := 1) (k := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 37) (a := 1) (k := 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 149) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)
  · exact S_two_mul_of_modCheck (p := 151) (a := 1) (k := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by native_decide)

/-- The number of certified doubling indices `≤ m` (the exponent in the lower
bound).  Recursive so the step `dcount (m+1) = dcount m + [m+1 ∈ indices]` is
definitional. -/
def dcount : ℕ → ℕ
  | 0 => 0
  | m + 1 => dcount m + (if (m + 1) ∈ doublingIndices then 1 else 0)

theorem dcount_succ (m : ℕ) :
    dcount (m + 1) = dcount m + (if (m + 1) ∈ doublingIndices then 1 else 0) := rfl

/-- The certified lower bound on `S`: the exact table for `m ≤ 83`, extended by
the doublings for `84 ≤ m ≤ 154`. -/
def sLowerBGMS (m : ℕ) : ℕ :=
  if m ≤ 83 then bgmsTable.getD m 0
  else bgmsTable.getD 83 0 * 2 ^ dcount m

/-- Chaining lemma: from `S 83` the doublings and monotonicity give
`S(83)·2^(dcount m) ≤ S m` for `83 ≤ m ≤ 154`. -/
theorem sLower_chain (m : ℕ) (hm : 83 ≤ m) :
    m ≤ 154 → bgmsTable.getD 83 0 * 2 ^ dcount m ≤ S m := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro _
    rw [show dcount 83 = 0 from by decide, pow_zero, mul_one]
    exact (bgmsSTable 83 (by norm_num)).ge
  | succ m hm ih =>
    intro hm1
    have ihm := ih (by omega)
    by_cases hmem : (m + 1) ∈ doublingIndices
    · have hdbl : S (m + 1) = 2 * S m := by
        have h := doubling_holds (m + 1) hmem
        rwa [Nat.add_sub_cancel] at h
      rw [dcount_succ, if_pos hmem, pow_succ]
      calc bgmsTable.getD 83 0 * (2 ^ dcount m * 2)
          = 2 * (bgmsTable.getD 83 0 * 2 ^ dcount m) := by ring
        _ ≤ 2 * S m := Nat.mul_le_mul le_rfl ihm
        _ = S (m + 1) := hdbl.symm
    · rw [dcount_succ, if_neg hmem, Nat.add_zero]
      exact le_trans ihm (S_mono (by omega))

/-- **The certified lower bounds `S m ≥ sLowerBGMS m` for `m ≤ 154`.**  Equality
to the exact table below `84`, and the doubling ledger above it. -/
theorem S_ge_sLowerBGMS (m : ℕ) (hm : m ≤ 154) : sLowerBGMS m ≤ S m := by
  unfold sLowerBGMS
  split_ifs with h
  · exact (bgmsSTable m h).ge
  · exact sLower_chain m (by omega) hm

end Erdos320
