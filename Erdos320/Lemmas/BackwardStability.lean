/-
# Backward stability estimate (`lem:backward-stability`)

Formalizes the paper's Lemma "Backward stability estimate"
(`\label{lem:backward-stability}`, displayed equation
`\eqref{eq:backward-stability}`): given the backward differentiation
relations `H_{s+1}' = a_s (H_s + ρ_s)` and `Q_{s+1}' = a_s Q_s` on the
`h`-neighbourhood `I_h` of a compact interval `I = [α, β]`, with `a_s`
bounded below by `aInf > 0`, `H_s` monotone, `Q_s` Lipschitz, `ρ_s` bounded,
and `C ≥ 0`, the function `Z_s = H_s - C·Q_s` satisfies, on `I`,

  `‖Z_s‖_I ≤ ‖ρ_s‖_{I_h} + C · Lip_{I_h}(Q_s) · h + 2‖Z_{s+1}‖_{I_h} / (h · inf_{I_h} a_s)`.

**Formalization note.** The paper states the differential relations as
almost-everywhere derivative identities for absolutely continuous functions.
Here they are taken in the equivalent *integral form* (the fundamental
theorem of calculus for absolutely continuous functions), which is exactly
the form in which the lemma is applied downstream: for all `x ≤ y` in `I_h`,
`H_{s+1}(y) - H_{s+1}(x) = ∫_x^y a_s (H_s + ρ_s)` and similarly for `Q`.
Integrability of the two integrands on `I_h` is supplied as a hypothesis to
keep this lemma measure-light. The suprema / Lipschitz constant / infimum of
the paper's statement are replaced by arbitrary bounds `ρBound`, `LipQ`,
`aInf`, `Znorm` valid on `I_h`, which is an equivalent (and
application-friendly) phrasing.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Erdos320

/-- **Backward stability estimate** (paper `lem:backward-stability`,
`eq:backward-stability`). With `I = [α, β]` and `I_h = [α - h, β + h]`:
if `a_s ≥ aInf > 0` on `I_h`, `H_s` is monotone on `I_h`, `Q_s` is
`LipQ`-Lipschitz on `I_h`, `|ρ_s| ≤ ρBound` on `I_h`, `C ≥ 0`, the backward
differentiation relations hold in integral form on `I_h`, and
`|H_{s+1} - C·Q_{s+1}| ≤ Znorm` on `I_h`, then on `I`

  `|H_s - C·Q_s| ≤ ρBound + C·LipQ·h + 2·Znorm / (h·aInf)`. -/
theorem backward_stability
    {α β h C ρBound LipQ aInf Znorm : ℝ}
    (hh : 0 < h) (hC : 0 ≤ C)
    (aS HS QS Hnext Qnext ρS : ℝ → ℝ)
    -- `a_s ≥ aInf > 0` on `I_h = [α - h, β + h]`:
    (haInf : 0 < aInf)
    (ha : ∀ v ∈ Set.Icc (α - h) (β + h), aInf ≤ aS v)
    -- `H_s` monotone (nondecreasing) on `I_h`:
    (hHmono : MonotoneOn HS (Set.Icc (α - h) (β + h)))
    -- `Q_s` Lipschitz with constant `LipQ ≥ 0` on `I_h`:
    (hLipQ : 0 ≤ LipQ)
    (hQlip : ∀ v ∈ Set.Icc (α - h) (β + h), ∀ w ∈ Set.Icc (α - h) (β + h),
      |QS v - QS w| ≤ LipQ * |v - w|)
    -- `ρ_s` bounded on `I_h`:
    (hρ : ∀ v ∈ Set.Icc (α - h) (β + h), |ρS v| ≤ ρBound)
    -- integral form of `H_{s+1}' = a_s (H_s + ρ_s)` on `I_h`:
    (hHint : ∀ x ∈ Set.Icc (α - h) (β + h), ∀ y ∈ Set.Icc (α - h) (β + h), x ≤ y →
      Hnext y - Hnext x = ∫ t in x..y, aS t * (HS t + ρS t))
    -- integral form of `Q_{s+1}' = a_s Q_s` on `I_h`:
    (hQint : ∀ x ∈ Set.Icc (α - h) (β + h), ∀ y ∈ Set.Icc (α - h) (β + h), x ≤ y →
      Qnext y - Qnext x = ∫ t in x..y, aS t * QS t)
    -- integrability of the two integrands on `I_h`:
    (hint1 : IntervalIntegrable (fun t => aS t * (HS t + ρS t))
      MeasureTheory.volume (α - h) (β + h))
    (hint2 : IntervalIntegrable (fun t => aS t * QS t)
      MeasureTheory.volume (α - h) (β + h))
    -- bound on `Z_{s+1} = H_{s+1} - C·Q_{s+1}` on `I_h`:
    (hZnorm : ∀ v ∈ Set.Icc (α - h) (β + h), |Hnext v - C * Qnext v| ≤ Znorm) :
    ∀ u ∈ Set.Icc α β,
      |HS u - C * QS u| ≤ ρBound + C * LipQ * h + 2 * Znorm / (h * aInf) := by
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  -- memberships in `I_h`
  have hu_mem : u ∈ Set.Icc (α - h) (β + h) := ⟨by linarith, by linarith⟩
  have hup_mem : u + h ∈ Set.Icc (α - h) (β + h) := ⟨by linarith, by linarith⟩
  have hdn_mem : u - h ∈ Set.Icc (α - h) (β + h) := ⟨by linarith, by linarith⟩
  have hZnorm0 : 0 ≤ Znorm := (abs_nonneg _).trans (hZnorm u hu_mem)
  have hpos : 0 < h * aInf := mul_pos hh haInf
  -- shared final step: a one-sided bound `h·aInf·c ≤ 2·Znorm`, valid whenever
  -- `c ≥ 0`, yields `c ≤ 2·Znorm / (h·aInf)`; for `c < 0` the bound is trivial.
  have key : ∀ c : ℝ, (0 ≤ c → h * aInf * c ≤ 2 * Znorm) →
      c ≤ 2 * Znorm / (h * aInf) := by
    intro c hcase
    rcases le_or_gt 0 c with hc | hc
    · rw [le_div_iff₀ hpos]
      linarith [hcase hc]
    · exact hc.le.trans (div_nonneg (by linarith) hpos.le)
  -- restricted integrability of the combined integrand on the two half-windows
  have hsub_up : Set.uIcc u (u + h) ⊆ Set.uIcc (α - h) (β + h) := by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  have hsub_dn : Set.uIcc (u - h) u ⊆ Set.uIcc (α - h) (β + h) := by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  have hi_up : IntervalIntegrable
      (fun t => aS t * (HS t + ρS t) - C * (aS t * QS t))
      MeasureTheory.volume u (u + h) :=
    (hint1.mono_set hsub_up).sub ((hint2.mono_set hsub_up).const_mul C)
  have hi_dn : IntervalIntegrable
      (fun t => aS t * (HS t + ρS t) - C * (aS t * QS t))
      MeasureTheory.volume (u - h) u :=
    (hint1.mono_set hsub_dn).sub ((hint2.mono_set hsub_dn).const_mul C)
  -- the combined integral identity for `Z_{s+1} = H_{s+1} - C·Q_{s+1}`
  have hZint : ∀ x ∈ Set.Icc (α - h) (β + h), ∀ y ∈ Set.Icc (α - h) (β + h), x ≤ y →
      IntervalIntegrable (fun t => aS t * (HS t + ρS t) - C * (aS t * QS t))
        MeasureTheory.volume x y →
      (Hnext y - C * Qnext y) - (Hnext x - C * Qnext x)
        = ∫ t in x..y, (aS t * (HS t + ρS t) - C * (aS t * QS t)) := by
    intro x hx y hy hxy hixy
    have hsub : Set.uIcc x y ⊆ Set.uIcc (α - h) (β + h) := by
      rw [Set.uIcc_of_le hxy, Set.uIcc_of_le (by linarith [hx.1, hy.2])]
      exact Set.Icc_subset_Icc hx.1 hy.2
    have hi1 := hint1.mono_set hsub
    have hi2 := (hint2.mono_set hsub).const_mul C
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
      ← hHint x hx y hy hxy, ← hQint x hx y hy hxy]
    ring
  -- upper bound for `Z_s(u)`, via the window `[u, u + h]`
  have hupper : HS u - C * QS u - C * LipQ * h - ρBound ≤ 2 * Znorm / (h * aInf) := by
    apply key
    intro hc
    -- pointwise lower bound for the integrand on `[u, u + h]`
    have hpoint : ∀ t ∈ Set.Icc u (u + h),
        aInf * (HS u - C * QS u - C * LipQ * h - ρBound)
          ≤ aS t * (HS t + ρS t) - C * (aS t * QS t) := by
      intro t ht
      have ht_mem : t ∈ Set.Icc (α - h) (β + h) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hHS : HS u ≤ HS t := hHmono hu_mem ht_mem ht.1
      have hQb : |QS t - QS u| ≤ LipQ * h := by
        calc |QS t - QS u| ≤ LipQ * |t - u| := hQlip t ht_mem u hu_mem
          _ ≤ LipQ * h := by
            apply mul_le_mul_of_nonneg_left _ hLipQ
            rw [abs_of_nonneg (by linarith [ht.1])]
            linarith [ht.2]
      have hCQ : C * (QS t - QS u) ≤ C * (LipQ * h) :=
        mul_le_mul_of_nonneg_left (abs_le.mp hQb).2 hC
      have hρt := (abs_le.mp (hρ t ht_mem)).1
      have hgt : HS u - C * QS u - C * LipQ * h - ρBound
          ≤ (HS t - C * QS t) + ρS t := by linarith
      have hmul : aInf * (HS u - C * QS u - C * LipQ * h - ρBound)
          ≤ aS t * ((HS t - C * QS t) + ρS t) :=
        mul_le_mul (ha t ht_mem) hgt hc (haInf.le.trans (ha t ht_mem))
      linarith [hmul]
    -- integrate the pointwise bound
    have hint_lb : h * (aInf * (HS u - C * QS u - C * LipQ * h - ρBound))
        ≤ ∫ t in u..(u + h), (aS t * (HS t + ρS t) - C * (aS t * QS t)) := by
      calc h * (aInf * (HS u - C * QS u - C * LipQ * h - ρBound))
          = ((u + h) - u) • (aInf * (HS u - C * QS u - C * LipQ * h - ρBound)) := by
            rw [smul_eq_mul]; ring
        _ = ∫ _ in u..(u + h), aInf * (HS u - C * QS u - C * LipQ * h - ρBound) :=
            (intervalIntegral.integral_const _).symm
        _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
            (intervalIntegrable_const) hi_up hpoint
    have hid := hZint u hu_mem (u + h) hup_mem (by linarith) hi_up
    have hb1 := (abs_le.mp (hZnorm (u + h) hup_mem)).2
    have hb2 := (abs_le.mp (hZnorm u hu_mem)).1
    rw [← hid] at hint_lb
    linarith
  -- lower bound for `Z_s(u)`, via the window `[u - h, u]`
  have hlower : -(HS u - C * QS u) - C * LipQ * h - ρBound ≤ 2 * Znorm / (h * aInf) := by
    apply key
    intro hc
    -- pointwise upper bound for the integrand on `[u - h, u]`
    have hpoint : ∀ t ∈ Set.Icc (u - h) u,
        aS t * (HS t + ρS t) - C * (aS t * QS t)
          ≤ aInf * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound)) := by
      intro t ht
      have ht_mem : t ∈ Set.Icc (α - h) (β + h) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hHS : HS t ≤ HS u := hHmono ht_mem hu_mem ht.2
      have hQb : |QS t - QS u| ≤ LipQ * h := by
        calc |QS t - QS u| ≤ LipQ * |t - u| := hQlip t ht_mem u hu_mem
          _ ≤ LipQ * h := by
            apply mul_le_mul_of_nonneg_left _ hLipQ
            rw [abs_of_nonpos (by linarith [ht.2])]
            linarith [ht.1]
      have hCQ : C * (QS u - QS t) ≤ C * (LipQ * h) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hQb).1]) hC
      have hρt := (abs_le.mp (hρ t ht_mem)).2
      have hlt : (HS t - C * QS t) + ρS t
          ≤ -(-(HS u - C * QS u) - C * LipQ * h - ρBound) := by linarith
      have haSt : 0 ≤ aS t := haInf.le.trans (ha t ht_mem)
      have hmul1 : aS t * ((HS t - C * QS t) + ρS t)
          ≤ aS t * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound)) :=
        mul_le_mul_of_nonneg_left hlt haSt
      have hmul2 : aS t * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound))
          ≤ aInf * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound)) :=
        mul_le_mul_of_nonpos_right (ha t ht_mem) (by linarith)
      linarith [hmul1, hmul2]
    -- integrate the pointwise bound
    have hint_ub : (∫ t in (u - h)..u, (aS t * (HS t + ρS t) - C * (aS t * QS t)))
        ≤ h * (aInf * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound))) := by
      calc (∫ t in (u - h)..u, (aS t * (HS t + ρS t) - C * (aS t * QS t)))
          ≤ ∫ _ in (u - h)..u, aInf * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound)) :=
            intervalIntegral.integral_mono_on (by linarith) hi_dn
              (intervalIntegrable_const) hpoint
        _ = (u - (u - h)) • (aInf * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound))) :=
            intervalIntegral.integral_const _
        _ = h * (aInf * (-(-(HS u - C * QS u) - C * LipQ * h - ρBound))) := by
            rw [smul_eq_mul]; ring
    have hid := hZint (u - h) hdn_mem u hu_mem (by linarith) hi_dn
    have hb1 := (abs_le.mp (hZnorm (u - h) hdn_mem)).2
    have hb2 := (abs_le.mp (hZnorm u hu_mem)).1
    rw [← hid] at hint_ub
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos320
