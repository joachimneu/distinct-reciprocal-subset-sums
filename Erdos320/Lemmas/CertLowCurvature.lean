import Erdos320.Lemmas.CoreClosedForm
import Erdos320.Lemmas.PhaseEnclosure
import Erdos320.Lemmas.CertificateTransfer

/-!
# Certificate `comp:low`, eq. `low-curvature`, proved in Lean

On every low chord window `[0.96·x(f), 1.04·x(f)]`, `f ∈ [2.78, 2.80]`, the
core profile `q̃` has positive slope, nonpositive second derivative, and
logarithmic curvature `−ξ q̃''(ξ)/q̃'(ξ) < 1.0601`
— tighter than the `1.061` displayed in `eq:low-curvature`, leaving headroom
for the core→limit transfer in `CertificateConsumers.lean`.  The paper's
display block carries only the slope-positivity line and the curvature bound
`eq:low-curvature`; the nonpositive-second-derivative conjunct proved here is
extra strength with no displayed counterpart, needed for the
slope-monotonicity endpoint reduction.  The package is
proved inside Lean by the same
technique as `CertLowQ4Positive.lean` / `CertLowSlopeMargin.lean`: the chain-rule
identities of `CertificateTransfer.lean` reduce `q̃'`, `q̃''` to the reference
core derivatives `Q̃₄'`, `Q̃₄''` at `u = log₃ ξ`, whose closed forms
(`CoreClosedForm.lean`) are bounded by the explicit rational `E`-enclosures of
`PhaseEnclosure.lean`.

For `f ∈ [2.78, 2.80]` the whole window lands in `ξ ∈ [9 725 449, 10 632 947]`,
where the enclosures give `Q̃₄'(u) ∈ [6.24, 6.29]`, `Q̃₄''(u) ∈ [8.89, 8.98]`,
`log ξ ∈ [16.0903, 16.1795]`, `log₂ ξ ∈ [2.7782, 2.7837]`.  With
`D = ξ·log ξ·log₂ ξ` and `P = log ξ·log₂ ξ + log₂ ξ + 1` the chain rule gives
`q̃'(ξ) = Q̃₄'/D` and `q̃''(ξ) = (Q̃₄'' − Q̃₄'·P)/D²`, from which the three
conjuncts follow: `Q̃₄' > 0`; `Q̃₄'' ≤ Q̃₄'·P` (since `P ≥ 48`, `Q̃₄'·P ≥ 6.24·48 > 299`);
and the polynomial margin `Q̃₄'·(log₂ξ+1) − Q̃₄'' < 0.0601·Q̃₄'·logξ·log₂ξ`
(LHS ≤ 14.92 < 16.76 ≤ RHS).

`Q̃₄'`, `Q̃₄''` are bounded (in the two private lemmas below) by the
**grouped-form** route of `CertLowSlopeMargin.lean`: the closed form is rewritten
as a decoupled leading part plus a remainder over `E₁²E₂²E₃`, the leading part is
bounded termwise via reciprocal enclosures, and the remainder (with
`E₃ = ξ ≥ 9.7·10⁶`) is negligible.

The theorem `lowCurvatureCert` certifies this three-conjunct core-level
package on exactly the paper's family of low chord windows.
-/

namespace Erdos320

set_option maxHeartbeats 2000000 in
/-- Enclosure `Q̃₄'(log₃ ξ) ∈ [6.24, 6.29]` on the enlarged low window. -/
private theorem cert_lowCurv_QpBounds {ξ : ℝ} (hlo : (9725449 : ℝ) ≤ ξ)
    (hhi : ξ ≤ 10632947) :
    (6.24 : ℝ) ≤ deriv QrefCore4 (iteratedLog 3 ξ)
      ∧ deriv QrefCore4 (iteratedLog 3 ξ) ≤ 6.29 := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith [cert_one_lt_iteratedLog_three hξ39]
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_W hlo hhi
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3eq⟩ := phaseEnclosure_E_W hlo hhi
  have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 ξ with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1ne : e1 ≠ 0 := he1pos.ne'
  have he2ne : e2 ≠ 0 := he2pos.ne'
  have he3ne : e3 ≠ 0 := he3pos.ne'
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  have he3lo : (9725449 : ℝ) ≤ e3 := by rw [he3eq]; exact hlo
  have hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hden_lo : (1.9e10 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (2.778213 : ℝ) ^ 2 * 16.090256 ^ 2 * 9725449 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
      gcongr
    nlinarith [h]
  -- remainder is nonnegative and negligible
  have hRp0 : (0 : ℝ) ≤ 2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3 := by
    have b1 : (2.778213 : ℝ) ^ 3 * 16.090256 ^ 3 ≤ e1 ^ 3 * e2 ^ 3 := by gcongr
    have b2 : (1.021808 : ℝ) * 2.778213 ^ 4 * 16.090256 ^ 3 ≤ u * e1 ^ 4 * e2 ^ 3 := by gcongr
    have n1 : e1 ^ 2 ≤ (2.783744 : ℝ) ^ 2 := by gcongr
    have n2 : e1 ^ 2 * e2 ^ 2 ≤ (2.783744 : ℝ) ^ 2 * 16.179468 ^ 2 := by gcongr
    have n3 : e1 ^ 3 * e2 ^ 2 ≤ (2.783744 : ℝ) ^ 3 * 16.179468 ^ 2 := by gcongr
    have n4 : u * e1 ^ 3 * e2 ^ 2 ≤ (1.023797 : ℝ) * 2.783744 ^ 3 * 16.179468 ^ 2 := by gcongr
    have hpos : (0 : ℝ) ≤ 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 := by
      nlinarith [b1, mul_nonneg he1nn he2nn,
        mul_nonneg (mul_nonneg hunn (pow_nonneg he1nn 3)) (pow_nonneg he2nn 3)]
    nlinarith [b1, b2, n1, n2, n3, n4, hpos]
  have hRpden_lo : (0 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) :=
    div_nonneg hRp0 hden_pos.le
  have hRpden_hi : (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) ≤ 0.024 := by
    rw [div_le_iff₀ hden_pos]
    have hp : 2 + 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3
        ≤ 2 + 2 * 2.783744 + 2.783744 * 16.179468 + 2 * 2.783744 ^ 3
            + 2.783744 ^ 3 * 16.179468 + 2.783744 ^ 3 * 16.179468 ^ 3
            + 2 * 1.023797 * 2.783744 ^ 3 + 1.023797 * 2.783744 ^ 3 * 16.179468
            + 1.023797 * 2.783744 ^ 3 * 16.179468 ^ 3
            + 1.023797 * 2.783744 ^ 4 * 16.179468 ^ 3 := by gcongr
    have hn : (2.778213 : ℝ) ^ 2 + 2.778213 ^ 2 * 16.090256 ^ 2
        + 2.778213 ^ 3 * 16.090256 ^ 2 + 1.021808 * 2.778213 ^ 3 * 16.090256 ^ 2
        ≤ e1 ^ 2 + e1 ^ 2 * e2 ^ 2 + e1 ^ 3 * e2 ^ 2 + u * e1 ^ 3 * e2 ^ 2 := by gcongr
    nlinarith [hden_lo, hp, hn]
  -- grouped closed form (via the factored-out identity lemma)
  have hgroupP := cert_grouped_deriv_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroupP
  -- termwise reciprocal enclosures for the leading part
  have tb_ue1_lo : (2.838 : ℝ) ≤ u * e1 := by nlinarith [hulo, he1lo, hu0, he1pos]
  have tb_ue1_hi : u * e1 ≤ 2.851 := by nlinarith [huhi, he1hi, hu0, he1pos]
  have tb_e1e2r_lo : (0.1717 : ℝ) ≤ e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he1lo, he2hi]
  have tb_e1e2r_hi : e1 / e2 ≤ 0.1731 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he1hi, he2lo]
  have tb_ue1e2r_lo : (0.1754 : ℝ) ≤ u * e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [tb_ue1_lo, he2hi]
  have tb_ue1e2r_hi : u * e1 / e2 ≤ 0.1772 := by
    rw [div_le_iff₀ he2pos]; nlinarith [tb_ue1_hi, he2lo]
  have tb_recip_lo : (0.0222 : ℝ) ≤ 1 / (e1 * e2) := by
    rw [le_div_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1hi, he2hi]
  have tb_recip_hi : 1 / (e1 * e2) ≤ 0.0224 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1lo, he2lo]
  refine ⟨?_, ?_⟩
  · rw [hgroupP]
    linarith [he1lo, tb_ue1_lo, tb_e1e2r_hi, tb_ue1e2r_hi, tb_recip_hi, hRpden_lo]
  · rw [hgroupP]
    linarith [he1hi, tb_ue1_hi, tb_e1e2r_lo, tb_ue1e2r_lo, tb_recip_lo, hRpden_hi]

set_option maxHeartbeats 2000000 in
/-- Enclosure `Q̃₄''(log₃ ξ) ∈ [8.89, 8.98]` on the enlarged low window. -/
private theorem cert_lowCurv_QppBounds {ξ : ℝ} (hlo : (9725449 : ℝ) ≤ ξ)
    (hhi : ξ ≤ 10632947) :
    (8.89 : ℝ) ≤ deriv (deriv QrefCore4) (iteratedLog 3 ξ)
      ∧ deriv (deriv QrefCore4) (iteratedLog 3 ξ) ≤ 8.98 := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith [cert_one_lt_iteratedLog_three hξ39]
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_W hlo hhi
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3eq⟩ := phaseEnclosure_E_W hlo hhi
  have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 ξ with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1ne : e1 ≠ 0 := he1pos.ne'
  have he2ne : e2 ≠ 0 := he2pos.ne'
  have he3ne : e3 ≠ 0 := he3pos.ne'
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  have he3lo : (9725449 : ℝ) ≤ e3 := by rw [he3eq]; exact hlo
  have hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hden_lo : (1.9e10 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (2.778213 : ℝ) ^ 2 * 16.090256 ^ 2 * 9725449 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
      gcongr
    nlinarith [h]
  -- `Q̃₄''` remainder is tiny in both directions
  have hRppden_hi : ((6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3)
      - (4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4)) / (e1 ^ 2 * e2 ^ 2 * e3) ≤ 0.02 := by
    rw [div_le_iff₀ hden_pos]
    have hp : 6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3
        ≤ 6 * 2.783744 ^ 3 + 3 * 2.783744 ^ 3 * 16.179468 + 3 * 2.783744 ^ 3 * 16.179468 ^ 3
            + 3 * 2.783744 ^ 4 * 16.179468 ^ 3 + 2 * 1.023797 * 2.783744 ^ 3
            + 1.023797 * 2.783744 ^ 3 * 16.179468 + 1.023797 * 2.783744 ^ 3 * 16.179468 ^ 3
            + 4 * 1.023797 * 2.783744 ^ 4 * 16.179468 ^ 3
            + 1.023797 * 2.783744 ^ 5 * 16.179468 ^ 3 := by gcongr
    have hn : (0 : ℝ) ≤ 4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4 := by
      have hb : (0 : ℝ) ≤ 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
          + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
          + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
          + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4 := by positivity
      linarith [hb]
    nlinarith [hden_lo, hp, hn]
  have hRppden_lo : (-0.02 : ℝ) ≤ ((6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3
        + 3 * e1 ^ 4 * e2 ^ 3 + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3
        + 4 * u * e1 ^ 4 * e2 ^ 3 + u * e1 ^ 5 * e2 ^ 3)
      - (4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4)) / (e1 ^ 2 * e2 ^ 2 * e3) := by
    rw [le_div_iff₀ hden_pos]
    have hn : 4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4
        ≤ 4 + 6 * 2.783744 + 3 * 2.783744 * 16.179468 + 4 * 2.783744 ^ 2
            + 3 * 2.783744 ^ 2 * 16.179468 + 2.783744 ^ 2 * 16.179468 ^ 2
            + 2 * 2.783744 ^ 3 * 16.179468 ^ 2 + 4 * 2.783744 ^ 4 + 3 * 2.783744 ^ 4 * 16.179468
            + 2.783744 ^ 4 * 16.179468 ^ 2 + 2.783744 ^ 4 * 16.179468 ^ 4
            + 1.023797 * 2.783744 ^ 3 * 16.179468 ^ 2 + 4 * 1.023797 * 2.783744 ^ 4
            + 3 * 1.023797 * 2.783744 ^ 4 * 16.179468 + 1.023797 * 2.783744 ^ 4 * 16.179468 ^ 2
            + 1.023797 * 2.783744 ^ 4 * 16.179468 ^ 4
            + 1.023797 * 2.783744 ^ 5 * 16.179468 ^ 4 := by gcongr
    have hp : (0 : ℝ) ≤ 6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3 := by positivity
    nlinarith [hden_lo, hn, hp]
  -- grouped closed form for `Q̃₄''`
  have hgroupPP := cert_grouped_deriv2_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroupPP
  -- termwise reciprocal enclosures for the leading part
  have hE1sq_lo : (7.7184 : ℝ) ≤ e1 ^ 2 := by nlinarith [he1lo, he1pos]
  have hE1sq_hi : e1 ^ 2 ≤ 7.7493 := by nlinarith [he1hi, he1pos]
  have huE1sq_lo : (7.886 : ℝ) ≤ u * e1 ^ 2 := by nlinarith [hulo, hE1sq_lo, hu0]
  have huE1sq_hi : u * e1 ^ 2 ≤ 7.934 := by nlinarith [huhi, hE1sq_hi, hu0]
  have tb_ue1_lo : (2.838 : ℝ) ≤ u * e1 := by nlinarith [hulo, he1lo, hu0, he1pos]
  have tb_ue1_hi : u * e1 ≤ 2.851 := by nlinarith [huhi, he1hi, hu0, he1pos]
  have tb_e1e2r_lo : (0.1717 : ℝ) ≤ e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he1lo, he2hi]
  have tb_e1e2r_hi : e1 / e2 ≤ 0.1731 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he1hi, he2lo]
  have tb_ue1e2r_lo : (0.1754 : ℝ) ≤ u * e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [tb_ue1_lo, he2hi]
  have tb_ue1e2r_hi : u * e1 / e2 ≤ 0.1772 := by
    rw [div_le_iff₀ he2pos]; nlinarith [tb_ue1_hi, he2lo]
  have tb_recip_lo : (0.0222 : ℝ) ≤ 1 / (e1 * e2) := by
    rw [le_div_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1hi, he2hi]
  have tb_recip_hi : 1 / (e1 * e2) ≤ 0.0224 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1lo, he2lo]
  have tb_e2recip_lo : (0.0618 : ℝ) ≤ 1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he2hi]
  have tb_e2recip_hi : 1 / e2 ≤ 0.0622 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he2lo]
  have tb_e1sqe2r_lo : (0.4770 : ℝ) ≤ e1 ^ 2 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [hE1sq_lo, he2hi]
  have tb_e1sqe2r_hi : e1 ^ 2 / e2 ≤ 0.4817 := by
    rw [div_le_iff₀ he2pos]; nlinarith [hE1sq_hi, he2lo]
  have tb_ue1sqe2r_lo : (0.4874 : ℝ) ≤ u * e1 ^ 2 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [huE1sq_lo, he2hi]
  have tb_ue1sqe2r_hi : u * e1 ^ 2 / e2 ≤ 0.4931 := by
    rw [div_le_iff₀ he2pos]; nlinarith [huE1sq_hi, he2lo]
  refine ⟨?_, ?_⟩
  · rw [hgroupPP]
    linarith [tb_recip_lo, tb_e2recip_lo, tb_e1e2r_hi, he1lo, tb_e1sqe2r_lo,
      tb_ue1e2r_hi, tb_ue1_lo, tb_ue1sqe2r_lo, hRppden_lo]
  · rw [hgroupPP]
    linarith [tb_recip_hi, tb_e2recip_hi, tb_e1e2r_lo, he1hi, tb_e1sqe2r_hi,
      tb_ue1e2r_lo, tb_ue1_hi, tb_ue1sqe2r_hi, hRppden_hi]

set_option maxHeartbeats 1000000 in
/-- **Proved core-level input to `eq:low-curvature`**:
on every low chord window `[0.96·x(f), 1.04·x(f)]`, `f ∈ [2.78, 2.80]`, the core
profile has positive slope, nonpositive second derivative, and logarithmic
curvature below `1.0601`. -/
theorem lowCurvatureCert (f : ℝ) (h1 : (2.78 : ℝ) ≤ f) (h2 : f ≤ 2.80)
    (ξ : ℝ) (hξ1 : 0.96 * lowBreakpointX f ≤ ξ) (hξ2 : ξ ≤ 1.04 * lowBreakpointX f) :
    0 < deriv qCore ξ ∧ deriv (deriv qCore) ξ ≤ 0 ∧
      -(ξ * deriv (deriv qCore) ξ) < 1.0601 * deriv qCore ξ := by
  -- `log N₀ ∈ [17.9999, 18.0001]` and its positivity
  obtain ⟨hLlo, hLhi⟩ := cert_log_N0_bounds
  have hLpos : (0 : ℝ) < Real.log 65659969 := by linarith
  -- window containment: `ξ ∈ [9 725 449, 10 632 947]`
  have hξlo : (9725449 : ℝ) ≤ ξ := by
    have h96 : (9725449 : ℝ) ≤ 0.96 * lowBreakpointX f := by
      rw [lowBreakpointX,
        show (0.96 : ℝ) * (65659969 * f / Real.log 65659969)
          = 0.96 * 65659969 * f / Real.log 65659969 from by ring, le_div_iff₀ hLpos]
      nlinarith [hLhi, h1]
    linarith [hξ1, h96]
  have hξhi : ξ ≤ 10632947 := by
    have h104 : 1.04 * lowBreakpointX f ≤ 10632947 := by
      rw [lowBreakpointX,
        show (1.04 : ℝ) * (65659969 * f / Real.log 65659969)
          = 1.04 * 65659969 * f / Real.log 65659969 from by ring, div_le_iff₀ hLpos]
      nlinarith [hLlo, h2]
    linarith [hξ2, h104]
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hξpos : (0 : ℝ) < ξ := by linarith
  -- log positivity from the phase enclosure
  obtain ⟨hLxlo, hLxhi, hLLxlo, hLLxhi, _, _⟩ := phaseEnclosure_W hξlo hξhi
  have hLxpos : (0 : ℝ) < Real.log ξ := by linarith
  have hLLxpos : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  -- the two enclosure packages for `Q̃₄'`, `Q̃₄''`
  obtain ⟨hQp_lo, hQp_hi⟩ := cert_lowCurv_QpBounds hξlo hξhi
  obtain ⟨hQpp_lo, hQpp_hi⟩ := cert_lowCurv_QppBounds hξlo hξhi
  set u := iteratedLog 3 ξ with hu
  have hQp_pos : (0 : ℝ) < deriv QrefCore4 u := by linarith [hQp_lo]
  have hDpos : (0 : ℝ) < ξ * Real.log ξ * Real.log (Real.log ξ) := by positivity
  -- chain-rule mapping identities
  have hd1 : deriv qCore ξ
      = deriv QrefCore4 u / (ξ * Real.log ξ * Real.log (Real.log ξ)) := by
    rw [cert_deriv_qCore_eq hξ39, ← hu, cert_iteratedLogThreeDeriv, div_eq_mul_inv]
  have hd2 : deriv (deriv qCore) ξ
      = (deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1))
        / (ξ * Real.log ξ * Real.log (Real.log ξ)) ^ 2 := by
    rw [cert_deriv2_qCore_eq hξ39, ← hu, cert_iteratedLogThreeDeriv,
      cert_iteratedLogThreeDeriv2]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- `0 < q̃'(ξ)`
    rw [hd1]
    exact div_pos hQp_pos hDpos
  · -- `q̃''(ξ) ≤ 0`
    rw [hd2]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hP48 : (48 : ℝ)
        ≤ Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1 := by
      nlinarith [hLxlo, hLLxlo]
    have hQpP : (6.24 : ℝ) * 48 ≤ deriv QrefCore4 u
        * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1) :=
      mul_le_mul hQp_lo hP48 (by norm_num) (by linarith [hQp_lo])
    linarith [hQpP, hQpp_hi]
  · -- `−ξ q̃''(ξ) < 1.0601 q̃'(ξ)`, the curvature bound
    have hstar : deriv QrefCore4 u * (Real.log (Real.log ξ) + 1)
        - deriv (deriv QrefCore4) u
        < 0.0601 * deriv QrefCore4 u * Real.log ξ * Real.log (Real.log ξ) := by
      have hRHSlow : (16.76 : ℝ)
          ≤ 0.0601 * (deriv QrefCore4 u * (Real.log ξ * Real.log (Real.log ξ))) := by
        have hprod : (6.24 : ℝ) * (16.090256 * 2.778213)
            ≤ deriv QrefCore4 u * (Real.log ξ * Real.log (Real.log ξ)) := by gcongr
        nlinarith [hprod]
      have hLHShigh : deriv QrefCore4 u * (Real.log (Real.log ξ) + 1)
          - deriv (deriv QrefCore4) u ≤ 14.92 := by
        have hprod2 : deriv QrefCore4 u * (Real.log (Real.log ξ) + 1)
            ≤ 6.29 * (2.783744 + 1) := by gcongr
        nlinarith [hprod2, hQpp_lo]
      nlinarith [hLHShigh, hRHSlow]
    have hb : (0 : ℝ) < 0.0601 * deriv QrefCore4 u * Real.log ξ * Real.log (Real.log ξ)
        - (deriv QrefCore4 u * (Real.log (Real.log ξ) + 1) - deriv (deriv QrefCore4) u) := by
      linarith [hstar]
    have hnumpos : (0 : ℝ) < 1.0601 * deriv QrefCore4 u
          * (ξ * Real.log ξ * Real.log (Real.log ξ))
        + ξ * (deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1)) := by
      nlinarith [mul_pos hξpos hb]
    rw [hd1, hd2]
    -- abstract field identity (fast: no expansion of the large denominator `D`)
    have hcomb := curvatureComb 1.0601 (deriv QrefCore4 u) (deriv (deriv QrefCore4) u)
      (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1) ξ
      (ξ * Real.log ξ * Real.log (Real.log ξ)) hDpos.ne'
    have hpos : (0 : ℝ) < 1.0601 * (deriv QrefCore4 u / (ξ * Real.log ξ * Real.log (Real.log ξ)))
        + ξ * ((deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1))
          / (ξ * Real.log ξ * Real.log (Real.log ξ)) ^ 2) := by
      rw [hcomb]; exact div_pos hnumpos (by positivity)
    linarith [hpos]

end Erdos320
