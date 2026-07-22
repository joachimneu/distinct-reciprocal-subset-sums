import Erdos320.Lemmas.CoreClosedForm
import Erdos320.Lemmas.PhaseEnclosureHigh
import Erdos320.Lemmas.CertificateTransfer

/-!
# Certificate `comp:high`, eq. `high-data`, proved in Lean

On every high chord
window `[0.999·x(f), 1.001·x(f)]`, `f ∈ [3.24, 46]`, the core profile `q̃` has a
strictly positive normalized slope `ξ·q̃'(ξ) > 0.0399`, nonpositive second
derivative, and logarithmic curvature `−ξ q̃''(ξ)/q̃'(ξ) < 1.0201`
(transcript `> 0.040`, `< 1.02`).  The
paper's display `eq:high-data` carries only the normalized-slope and
curvature bounds; the nonpositive-second-derivative conjunct proved here is
extra strength with no displayed counterpart, needed for the
slope-monotonicity endpoint reduction.  The package is proved inside Lean
by the same technique as the
low-window sibling `CertLowCurvature.lean`: the chain-rule identities of
`CertificateTransfer.lean` reduce `q̃'`, `q̃''` to the reference core derivatives
`Q̃₄'`, `Q̃₄''` at `u = log₃ ξ`, whose closed forms (`CoreClosedForm.lean`) are
bounded by the explicit rational `E`-enclosures of `PhaseEnclosureHigh.lean`.

For `f ∈ [3.24, 46]` the whole window lands in `ξ ∈ [8·10²⁶, 1.3·10²⁸]`, where
the enclosures give `Q̃₄'(u) ∈ [10.80, 10.97]`, `Q̃₄''(u) ∈ [14.52, 14.79]`,
`log ξ ∈ [61.94665, 64.73475]`, `log₂ ξ ∈ [4.12627, 4.1703]`.  With
`D = ξ·log ξ·log₂ ξ` and `P = log ξ·log₂ ξ + log₂ ξ + 1` the chain rule gives
`q̃'(ξ) = Q̃₄'/D` and `q̃''(ξ) = (Q̃₄'' − Q̃₄'·P)/D²`, from which:

* **Nonpositive curvature** `q̃'' ≤ 0`: `Q̃₄'' ≤ Q̃₄'·P` (since `P ≥ 260`,
  `Q̃₄'·P ≥ 2815`).
* **Log-curvature bound** the polynomial margin
  `Q̃₄'·(log₂ξ+1) − Q̃₄'' < 0.0201·Q̃₄'·logξ·log₂ξ` (LHS ≤ 42.2 < 55.4 ≤ RHS).
* **Positive normalized slope** `ξ·q̃'(ξ) = Q̃₄'/(logξ·log₂ξ)` is *decreasing* in
  `ξ` over the window (its derivative `q̃' + ξ q̃''` has numerator
  `ξ·(Q̃₄'' − Q̃₄'·(log₂ξ+1)) ≤ 0`), so its minimum sits at the right endpoint
  `B := 1.001·x(46) = 1.001·N₁·46/log N₁ ∈ [1.2004·10²⁸, 1.2009·10²⁸]`; there the
  sharp `H46` enclosure gives `Q̃₄'(u(B)) ≥ 10.84 > 10.755 = 0.0399·logξ·log₂ξ`,
  hence `ξ·q̃'(ξ) ≥ B·q̃'(B) > 0.0399`.

`Q̃₄'`, `Q̃₄''` are bounded (in the private lemmas below) by the **grouped-form**
route of `CertLowCurvature.lean`: the closed form is rewritten as a decoupled
leading part plus a remainder over `E₁²E₂²E₃`, whose numerator (with
`E₃ = ξ ≥ 8·10²⁶`) is negligible (`|remainder| ≤ 10⁻⁶`).

The theorem `highDataCert` certifies this three-conjunct core-level package
on exactly the paper's family of high chord windows; the core-to-limit
transfer to the displayed constants of `eq:high-data` (`0.0398`, `1.021`)
happens in `CertificateTransfer.lean`.
-/

namespace Erdos320

set_option maxHeartbeats 1200000 in
/-- Enclosure `Q̃₄'(log₃ ξ) ∈ [10.80, 10.97]` on the high window
`[8·10²⁶, 1.3·10²⁸]`. -/
private theorem cert_highCurv_QpBounds {ξ : ℝ} (hlo : (8e26 : ℝ) ≤ ξ)
    (hhi : ξ ≤ 1.3e28) :
    (10.80 : ℝ) ≤ deriv QrefCore4 (iteratedLog 3 ξ)
      ∧ deriv QrefCore4 (iteratedLog 3 ξ) ≤ 10.97 := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith [cert_one_lt_iteratedLog_three hξ39]
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_WH hlo hhi
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3eq⟩ := phaseEnclosure_E_WH hlo hhi
  have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 ξ with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  have he3lo : (8e26 : ℝ) ≤ e3 := by rw [he3eq]; exact hlo
  have hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hden_lo : (5e31 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (4.12627 : ℝ) ^ 2 * 61.94665 ^ 2 * 8e26 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by gcongr
    nlinarith [h]
  -- remainder numerator: bounded two-sided by ±10⁶, hence negligible over the denominator
  have hRp_ub : (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) ≤ 2e8 := by
    have hpos : 2 + 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3
        ≤ 2 + 2 * 4.1703 + 4.1703 * 64.73475 + 2 * 4.1703 ^ 3 + 4.1703 ^ 3 * 64.73475
            + 4.1703 ^ 3 * 64.73475 ^ 3 + 2 * 1.42799 * 4.1703 ^ 3
            + 1.42799 * 4.1703 ^ 3 * 64.73475 + 1.42799 * 4.1703 ^ 3 * 64.73475 ^ 3
            + 1.42799 * 4.1703 ^ 4 * 64.73475 ^ 3 := by gcongr
    have hneg : (0 : ℝ) ≤ e1 ^ 2 + e1 ^ 2 * e2 ^ 2 + e1 ^ 3 * e2 ^ 2 + u * e1 ^ 3 * e2 ^ 2 := by
      positivity
    linarith [hpos, hneg]
  have hRp_lb : (-1e6 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) := by
    have hpos0 : (0 : ℝ) ≤ 2 + 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3 := by
      positivity
    have hnegub : e1 ^ 2 + e1 ^ 2 * e2 ^ 2 + e1 ^ 3 * e2 ^ 2 + u * e1 ^ 3 * e2 ^ 2 ≤ 1e6 := by
      have h : e1 ^ 2 + e1 ^ 2 * e2 ^ 2 + e1 ^ 3 * e2 ^ 2 + u * e1 ^ 3 * e2 ^ 2
          ≤ 4.1703 ^ 2 + 4.1703 ^ 2 * 64.73475 ^ 2 + 4.1703 ^ 3 * 64.73475 ^ 2
            + 1.42799 * 4.1703 ^ 3 * 64.73475 ^ 2 := by gcongr
      linarith [h]
    linarith [hpos0, hnegub]
  have hRemP_ub : (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
        + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) ≤ 1e-6 := by
    rw [div_le_iff₀ hden_pos]; linarith [hRp_ub, hden_lo]
  have hRemP_lb : (-1e-6 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
        + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) := by
    rw [le_div_iff₀ hden_pos]; linarith [hRp_lb, hden_lo]
  -- grouped closed form (via the factored-out identity lemma)
  have hgroupP := cert_grouped_deriv_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroupP
  -- termwise reciprocal enclosures for the leading part
  have tb_ue1_lo : (5.848 : ℝ) ≤ u * e1 := by nlinarith [hulo, he1lo, hu0, he1pos]
  have tb_ue1_hi : u * e1 ≤ 5.9552 := by nlinarith [huhi, he1hi, hu0, he1pos]
  have tb_e1e2r_lo : (0.0637 : ℝ) ≤ e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he1lo, he2hi]
  have tb_e1e2r_hi : e1 / e2 ≤ 0.06733 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he1hi, he2lo]
  have tb_ue1e2r_lo : (0.0903 : ℝ) ≤ u * e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [tb_ue1_lo, he2hi]
  have tb_ue1e2r_hi : u * e1 / e2 ≤ 0.09614 := by
    rw [div_le_iff₀ he2pos]; nlinarith [tb_ue1_hi, he2lo]
  have tb_recip_lo : (0.0037 : ℝ) ≤ 1 / (e1 * e2) := by
    rw [le_div_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1hi, he2hi]
  have tb_recip_hi : 1 / (e1 * e2) ≤ 0.003913 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1lo, he2lo]
  refine ⟨?_, ?_⟩
  · rw [hgroupP]
    linarith [he1lo, tb_ue1_lo, tb_e1e2r_hi, tb_ue1e2r_hi, tb_recip_hi, hRemP_lb]
  · rw [hgroupP]
    linarith [he1hi, tb_ue1_hi, tb_e1e2r_lo, tb_ue1e2r_lo, tb_recip_lo, hRemP_ub]

set_option maxHeartbeats 1200000 in
/-- Two-sided bound `|remainder| ≤ 10⁻⁶` for the `Q̃₄''` grouped form, over the
high window's `E`-enclosures.  Factored out (own heartbeat budget) so the heavy
`gcongr`/`linarith` on the ~26-monomial numerator does not blow the budget of
`cert_highCurv_QppBounds`. -/
private theorem cert_highCurv_Qpp_remBounds {e1 e2 e3 u : ℝ}
    (he1hi : e1 ≤ 4.1703) (he2hi : e2 ≤ 64.73475) (huhi : u ≤ 1.42799)
    (he1nn : (0 : ℝ) ≤ e1) (he2nn : (0 : ℝ) ≤ e2) (hunn : (0 : ℝ) ≤ u)
    (hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3)
    (hden_lo : (5e31 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3) :
    ((6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3)
      - (4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4)) / (e1 ^ 2 * e2 ^ 2 * e3) ≤ 1e-6
    ∧ (-1e-6 : ℝ) ≤ ((6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3)
      - (4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4)) / (e1 ^ 2 * e2 ^ 2 * e3) := by
  have hRpp_ub : (6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3)
      - (4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4) ≤ 2e9 := by
    have hpos : 6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3
        ≤ 6 * 4.1703 ^ 3 + 3 * 4.1703 ^ 3 * 64.73475 + 3 * 4.1703 ^ 3 * 64.73475 ^ 3
            + 3 * 4.1703 ^ 4 * 64.73475 ^ 3 + 2 * 1.42799 * 4.1703 ^ 3
            + 1.42799 * 4.1703 ^ 3 * 64.73475 + 1.42799 * 4.1703 ^ 3 * 64.73475 ^ 3
            + 4 * 1.42799 * 4.1703 ^ 4 * 64.73475 ^ 3
            + 1.42799 * 4.1703 ^ 5 * 64.73475 ^ 3 := by gcongr
    have hneg : (0 : ℝ) ≤ 4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4 := by positivity
    linarith [hpos, hneg]
  have hRpp_lb : (-1e11 : ℝ) ≤ (6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3
        + 3 * e1 ^ 4 * e2 ^ 3 + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3
        + 4 * u * e1 ^ 4 * e2 ^ 3 + u * e1 ^ 5 * e2 ^ 3)
      - (4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4) := by
    have hpos0 : (0 : ℝ) ≤ 6 * e1 ^ 3 + 3 * e1 ^ 3 * e2 + 3 * e1 ^ 3 * e2 ^ 3 + 3 * e1 ^ 4 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + 4 * u * e1 ^ 4 * e2 ^ 3
        + u * e1 ^ 5 * e2 ^ 3 := by positivity
    have hnegub : 4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
        + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
        + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4 ≤ 1e11 := by
      have h : 4 + 6 * e1 + 3 * e1 * e2 + 4 * e1 ^ 2 + 3 * e1 ^ 2 * e2 + e1 ^ 2 * e2 ^ 2
          + 2 * e1 ^ 3 * e2 ^ 2 + 4 * e1 ^ 4 + 3 * e1 ^ 4 * e2 + e1 ^ 4 * e2 ^ 2 + e1 ^ 4 * e2 ^ 4
          + u * e1 ^ 3 * e2 ^ 2 + 4 * u * e1 ^ 4 + 3 * u * e1 ^ 4 * e2 + u * e1 ^ 4 * e2 ^ 2
          + u * e1 ^ 4 * e2 ^ 4 + u * e1 ^ 5 * e2 ^ 4
          ≤ 4 + 6 * 4.1703 + 3 * 4.1703 * 64.73475 + 4 * 4.1703 ^ 2 + 3 * 4.1703 ^ 2 * 64.73475
              + 4.1703 ^ 2 * 64.73475 ^ 2 + 2 * 4.1703 ^ 3 * 64.73475 ^ 2 + 4 * 4.1703 ^ 4
              + 3 * 4.1703 ^ 4 * 64.73475 + 4.1703 ^ 4 * 64.73475 ^ 2 + 4.1703 ^ 4 * 64.73475 ^ 4
              + 1.42799 * 4.1703 ^ 3 * 64.73475 ^ 2 + 4 * 1.42799 * 4.1703 ^ 4
              + 3 * 1.42799 * 4.1703 ^ 4 * 64.73475 + 1.42799 * 4.1703 ^ 4 * 64.73475 ^ 2
              + 1.42799 * 4.1703 ^ 4 * 64.73475 ^ 4
              + 1.42799 * 4.1703 ^ 5 * 64.73475 ^ 4 := by gcongr
      linarith [h]
    linarith [hpos0, hnegub]
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hden_pos]; linarith [hRpp_ub, hden_lo]
  · rw [le_div_iff₀ hden_pos]; linarith [hRpp_lb, hden_lo]

set_option maxHeartbeats 1200000 in
/-- Enclosure `Q̃₄''(log₃ ξ) ∈ [14.52, 14.79]` on the high window
`[8·10²⁶, 1.3·10²⁸]`. -/
private theorem cert_highCurv_QppBounds {ξ : ℝ} (hlo : (8e26 : ℝ) ≤ ξ)
    (hhi : ξ ≤ 1.3e28) :
    (14.52 : ℝ) ≤ deriv (deriv QrefCore4) (iteratedLog 3 ξ)
      ∧ deriv (deriv QrefCore4) (iteratedLog 3 ξ) ≤ 14.79 := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith [cert_one_lt_iteratedLog_three hξ39]
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_WH hlo hhi
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3eq⟩ := phaseEnclosure_E_WH hlo hhi
  have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 ξ with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  have he3lo : (8e26 : ℝ) ≤ e3 := by rw [he3eq]; exact hlo
  have hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hden_lo : (5e31 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (4.12627 : ℝ) ^ 2 * 61.94665 ^ 2 * 8e26 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by gcongr
    nlinarith [h]
  -- the two-sided remainder bound (heavy poly work offloaded to its own lemma)
  obtain ⟨hrem_ub, hrem_lb⟩ :=
    cert_highCurv_Qpp_remBounds he1hi he2hi huhi he1nn he2nn hunn hden_pos hden_lo
  -- grouped closed form for `Q̃₄''` (via the factored-out identity lemma)
  have hgroupPP := cert_grouped_deriv2_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroupPP
  -- termwise reciprocal enclosures for the leading part
  have hE1sq_lo : (17.026 : ℝ) ≤ e1 ^ 2 := by nlinarith [he1lo, he1pos]
  have hE1sq_hi : e1 ^ 2 ≤ 17.392 := by nlinarith [he1hi, he1pos]
  have huE1sq_lo : (24.13 : ℝ) ≤ u * e1 ^ 2 := by nlinarith [hulo, hE1sq_lo, hu0]
  have huE1sq_hi : u * e1 ^ 2 ≤ 24.835 := by nlinarith [huhi, hE1sq_hi, hu0]
  have tb_ue1_lo : (5.848 : ℝ) ≤ u * e1 := by nlinarith [hulo, he1lo, hu0, he1pos]
  have tb_ue1_hi : u * e1 ≤ 5.9552 := by nlinarith [huhi, he1hi, hu0, he1pos]
  have tb_e1e2r_lo : (0.0637 : ℝ) ≤ e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he1lo, he2hi]
  have tb_e1e2r_hi : e1 / e2 ≤ 0.06733 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he1hi, he2lo]
  have tb_ue1e2r_lo : (0.0903 : ℝ) ≤ u * e1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [tb_ue1_lo, he2hi]
  have tb_ue1e2r_hi : u * e1 / e2 ≤ 0.09614 := by
    rw [div_le_iff₀ he2pos]; nlinarith [tb_ue1_hi, he2lo]
  have tb_recip_lo : (0.0037 : ℝ) ≤ 1 / (e1 * e2) := by
    rw [le_div_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1hi, he2hi]
  have tb_recip_hi : 1 / (e1 * e2) ≤ 0.003913 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1lo, he2lo]
  have tb_e2recip_lo : (0.01544 : ℝ) ≤ 1 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [he2hi]
  have tb_e2recip_hi : 1 / e2 ≤ 0.016143 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he2lo]
  have tb_e1sqe2r_lo : (0.2630 : ℝ) ≤ e1 ^ 2 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [hE1sq_lo, he2hi]
  have tb_e1sqe2r_hi : e1 ^ 2 / e2 ≤ 0.28075 := by
    rw [div_le_iff₀ he2pos]; nlinarith [hE1sq_hi, he2lo]
  have tb_ue1sqe2r_lo : (0.3727 : ℝ) ≤ u * e1 ^ 2 / e2 := by
    rw [le_div_iff₀ he2pos]; nlinarith [huE1sq_lo, he2hi]
  have tb_ue1sqe2r_hi : u * e1 ^ 2 / e2 ≤ 0.40091 := by
    rw [div_le_iff₀ he2pos]; nlinarith [huE1sq_hi, he2lo]
  -- the leading part sits in `[14.520001, 14.789999]`; combine with the `±10⁻⁶`
  -- remainder via `add_le_add` (keeps the remainder fraction opaque to `linarith`)
  refine ⟨?_, ?_⟩
  · rw [hgroupPP]
    have hlead : (14.520001 : ℝ) ≤ 1 / (e1 * e2) + 1 / e2 - 2 * (e1 / e2) + 2 * e1
        + e1 ^ 2 / e2 - u * e1 / e2 + u * e1 + u * e1 ^ 2 / e2 := by
      linarith [tb_recip_lo, tb_e2recip_lo, tb_e1e2r_hi, he1lo, tb_e1sqe2r_lo,
        tb_ue1e2r_hi, tb_ue1_lo, tb_ue1sqe2r_lo]
    exact le_trans (by norm_num) (add_le_add hlead hrem_lb)
  · rw [hgroupPP]
    have hlead : 1 / (e1 * e2) + 1 / e2 - 2 * (e1 / e2) + 2 * e1 + e1 ^ 2 / e2
        - u * e1 / e2 + u * e1 + u * e1 ^ 2 / e2 ≤ (14.789999 : ℝ) := by
      linarith [tb_recip_hi, tb_e2recip_hi, tb_e1e2r_lo, he1hi, tb_e1sqe2r_hi,
        tb_ue1e2r_lo, tb_ue1_hi, tb_ue1sqe2r_hi]
    exact le_trans (add_le_add hlead hrem_ub) (by norm_num)

set_option maxHeartbeats 1200000 in
/-- Endpoint lower bound `Q̃₄'(log₃ ξ) ≥ 10.84` on the sharp right-endpoint
window `H46 = [1.2004·10²⁸, 1.2009·10²⁸]` around `x(46) = N₁·46/log N₁`. -/
private theorem cert_highData_QpB_lb {ξ : ℝ} (hlo : (1.2004e28 : ℝ) ≤ ξ)
    (hhi : ξ ≤ 1.2009e28) :
    (10.84 : ℝ) ≤ deriv QrefCore4 (iteratedLog 3 ξ) := by
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hu0 : (0 : ℝ) < iteratedLog 3 ξ := by linarith [cert_one_lt_iteratedLog_three hξ39]
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_H46 hlo hhi
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3eq⟩ := phaseEnclosure_E_H46 hlo hhi
  have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
  set u := iteratedLog 3 ξ with hu
  set e1 := E 1 u with he1def
  set e2 := E 2 u with he2def
  set e3 := E 3 u with he3def
  have he1nn : (0 : ℝ) ≤ e1 := he1pos.le
  have he2nn : (0 : ℝ) ≤ e2 := he2pos.le
  have hunn : (0 : ℝ) ≤ u := hu0.le
  have he3lo : (1.2004e28 : ℝ) ≤ e3 := by rw [he3eq]; exact hlo
  have hden_pos : (0 : ℝ) < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  have hden_lo : (8e32 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (4.169063 : ℝ) ^ 2 * 64.6549 ^ 2 * 1.2004e28 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by gcongr
    nlinarith [h]
  have hRp_lb : (-1e6 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
      + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
      + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
      + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) := by
    have hpos0 : (0 : ℝ) ≤ 2 + 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3 := by
      positivity
    have hnegub : e1 ^ 2 + e1 ^ 2 * e2 ^ 2 + e1 ^ 3 * e2 ^ 2 + u * e1 ^ 3 * e2 ^ 2 ≤ 1e6 := by
      have h : e1 ^ 2 + e1 ^ 2 * e2 ^ 2 + e1 ^ 3 * e2 ^ 2 + u * e1 ^ 3 * e2 ^ 2
          ≤ 4.169074 ^ 2 + 4.169074 ^ 2 * 64.6555 ^ 2 + 4.169074 ^ 3 * 64.6555 ^ 2
            + 1.427696 * 4.169074 ^ 3 * 64.6555 ^ 2 := by gcongr
      linarith [h]
    linarith [hpos0, hnegub]
  have hRemP_lb : (-1e-6 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
        + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 2 * e2 ^ 2 * e3) := by
    rw [le_div_iff₀ hden_pos]; linarith [hRp_lb, hden_lo]
  have hgroupP := cert_grouped_deriv_QrefCore4 hu0
  rw [← he1def, ← he2def, ← he3def] at hgroupP
  have tb_ue1_lo : (5.952 : ℝ) ≤ u * e1 := by nlinarith [hulo, he1lo, hu0, he1pos]
  have tb_e1e2r_hi : e1 / e2 ≤ 0.0645 := by
    rw [div_le_iff₀ he2pos]; nlinarith [he1hi, he2lo]
  have tb_ue1e2r_hi : u * e1 / e2 ≤ 0.0921 := by
    rw [div_le_iff₀ he2pos]; nlinarith [tb_ue1_lo, huhi, he1hi, he2lo, hu0, he1pos]
  have tb_recip_hi : 1 / (e1 * e2) ≤ 0.00372 := by
    rw [div_le_iff₀ (mul_pos he1pos he2pos)]; nlinarith [he1lo, he2lo]
  rw [hgroupP]
  linarith [he1lo, tb_ue1_lo, tb_e1e2r_hi, tb_ue1e2r_hi, tb_recip_hi, hRemP_lb]

/-- The map `y ↦ y · q̃'(y)` is differentiable on the working range, with
derivative `q̃'(y) + y·q̃''(y)` (product rule). -/
private theorem cert_highData_hasDerivAt_slope {x : ℝ} (hx39 : (3.9e6 : ℝ) < x) :
    HasDerivAt (fun y => y * deriv qCore y)
      (deriv qCore x + x * deriv (deriv qCore) x) x := by
  have h := (hasDerivAt_id x).mul (cert_hasDerivAt_deriv_qCore_self hx39)
  simp only [one_mul, id_eq] at h
  exact h

set_option maxHeartbeats 1200000 in
/-- The slope of `y ↦ y·q̃'(y)` is nonpositive on the high window, i.e.
`q̃'(x) + x·q̃''(x) ≤ 0`, because its `D²`-scaled numerator is
`x·(Q̃₄'' − Q̃₄'·(log₂x+1)) ≤ 0`. -/
private theorem cert_highData_slopeDeriv_nonpos {x : ℝ} (hlo : (8e26 : ℝ) ≤ x)
    (hhi : x ≤ 1.3e28) : deriv (fun y => y * deriv qCore y) x ≤ 0 := by
  have hx39 : (3.9e6 : ℝ) < x := by linarith
  rw [(cert_highData_hasDerivAt_slope hx39).deriv]
  obtain ⟨hLxlo, _, hLLxlo, _, _, _⟩ := phaseEnclosure_WH hlo hhi
  have hLxpos : (0 : ℝ) < Real.log x := by linarith
  have hLLxpos : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  obtain ⟨hQp_lo, _⟩ := cert_highCurv_QpBounds hlo hhi
  obtain ⟨_, hQpp_hi⟩ := cert_highCurv_QppBounds hlo hhi
  set u := iteratedLog 3 x with hu
  have hDpos : (0 : ℝ) < x * Real.log x * Real.log (Real.log x) := by positivity
  have hd1 : deriv qCore x
      = deriv QrefCore4 u / (x * Real.log x * Real.log (Real.log x)) := by
    rw [cert_deriv_qCore_eq hx39, ← hu, cert_iteratedLogThreeDeriv, div_eq_mul_inv]
  have hd2 : deriv (deriv qCore) x
      = (deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log x * Real.log (Real.log x) + Real.log (Real.log x) + 1))
        / (x * Real.log x * Real.log (Real.log x)) ^ 2 := by
    rw [cert_deriv2_qCore_eq hx39, ← hu, cert_iteratedLogThreeDeriv,
      cert_iteratedLogThreeDeriv2]
    field_simp
    ring
  rw [hd1, hd2]
  -- `Q̃₄'' ≤ Q̃₄'·(log₂x+1)`: RHS ≥ 10.80·5 = 54, LHS ≤ 14.79
  have hLL1 : (5 : ℝ) ≤ Real.log (Real.log x) + 1 := by linarith
  have hQpLL : (54 : ℝ) ≤ deriv QrefCore4 u * (Real.log (Real.log x) + 1) := by
    nlinarith [hQp_lo, hLL1]
  have hkey : deriv (deriv QrefCore4) u
      ≤ deriv QrefCore4 u * (Real.log (Real.log x) + 1) := by linarith [hQpp_hi, hQpLL]
  rw [show deriv QrefCore4 u / (x * Real.log x * Real.log (Real.log x))
        + x * ((deriv (deriv QrefCore4) u
            - deriv QrefCore4 u
              * (Real.log x * Real.log (Real.log x) + Real.log (Real.log x) + 1))
          / (x * Real.log x * Real.log (Real.log x)) ^ 2)
      = (deriv QrefCore4 u * (x * Real.log x * Real.log (Real.log x))
          + x * (deriv (deriv QrefCore4) u
            - deriv QrefCore4 u
              * (Real.log x * Real.log (Real.log x) + Real.log (Real.log x) + 1)))
        / (x * Real.log x * Real.log (Real.log x)) ^ 2 from by
    field_simp]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  rw [show deriv QrefCore4 u * (x * Real.log x * Real.log (Real.log x))
        + x * (deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log x * Real.log (Real.log x) + Real.log (Real.log x) + 1))
      = x * (deriv (deriv QrefCore4) u
          - deriv QrefCore4 u * (Real.log (Real.log x) + 1)) from by ring]
  exact mul_nonpos_of_nonneg_of_nonpos hxpos.le (by linarith [hkey])

set_option maxHeartbeats 1200000 in
/-- **Proved core-level input to `eq:high-data`**:
on every high chord window `[0.999·x(f), 1.001·x(f)]`, `f ∈ [3.24, 46]`, the core
profile has normalized slope `ξ·q̃'(ξ) > 0.0399`, nonpositive second derivative,
and logarithmic curvature below `1.0201`. -/
theorem highDataCert (f : ℝ) (h1 : (3.24 : ℝ) ≤ f) (h2 : f ≤ 46)
    (ξ : ℝ) (hξ1 : 0.999 * highBreakpointX f ≤ ξ) (hξ2 : ξ ≤ 1.001 * highBreakpointX f) :
    0.0399 < ξ * deriv qCore ξ ∧ deriv (deriv qCore) ξ ≤ 0 ∧
      -(ξ * deriv (deriv qCore) ξ) < 1.0201 * deriv qCore ξ := by
  obtain ⟨hL1, hL2⟩ := cert_log_N1_bounds
  have hLpos : (0 : ℝ) < Real.log 16948892444103337141417836114 := by linarith
  -- window lower bound `ξ ≥ 8·10²⁶`
  have hξlo : (8e26 : ℝ) ≤ ξ := by
    have hb : (8e26 : ℝ) ≤ 0.999 * highBreakpointX f := by
      rw [highBreakpointX,
        show (0.999 : ℝ) * (16948892444103337141417836114 * f
              / Real.log 16948892444103337141417836114)
          = 0.999 * 16948892444103337141417836114 * f
              / Real.log 16948892444103337141417836114 from by ring,
        le_div_iff₀ hLpos]
      nlinarith [hL2, h1]
    linarith [hξ1, hb]
  -- right endpoint `B = 1.001·x(46)`
  set B := 1.001 * highBreakpointX 46 with hBdef
  have hBlo : (1.2004e28 : ℝ) ≤ B := by
    rw [hBdef, highBreakpointX,
      show (1.001 : ℝ) * (16948892444103337141417836114 * 46
            / Real.log 16948892444103337141417836114)
        = 1.001 * 16948892444103337141417836114 * 46
            / Real.log 16948892444103337141417836114 from by ring,
      le_div_iff₀ hLpos]
    nlinarith [hL2]
  have hBhi : B ≤ 1.2009e28 := by
    rw [hBdef, highBreakpointX,
      show (1.001 : ℝ) * (16948892444103337141417836114 * 46
            / Real.log 16948892444103337141417836114)
        = 1.001 * 16948892444103337141417836114 * 46
            / Real.log 16948892444103337141417836114 from by ring,
      div_le_iff₀ hLpos]
    nlinarith [hL1]
  have hB_le : B ≤ 1.3e28 := by linarith
  have hB8 : (8e26 : ℝ) ≤ B := by linarith
  -- `ξ ≤ B` by monotonicity of `x(·)` in `f`
  have hξB : ξ ≤ B := by
    have hmono : 1.001 * highBreakpointX f ≤ B := by
      rw [hBdef, highBreakpointX, highBreakpointX,
        show (1.001 : ℝ) * (16948892444103337141417836114 * f
              / Real.log 16948892444103337141417836114)
          = 1.001 * 16948892444103337141417836114 * f
              / Real.log 16948892444103337141417836114 from by ring,
        show (1.001 : ℝ) * (16948892444103337141417836114 * 46
              / Real.log 16948892444103337141417836114)
          = 1.001 * 16948892444103337141417836114 * 46
              / Real.log 16948892444103337141417836114 from by ring,
        div_le_div_iff_of_pos_right hLpos]
      nlinarith [h2]
    linarith [hξ2, hmono]
  have hξhi : ξ ≤ 1.3e28 := by linarith
  have hξ39 : (3.9e6 : ℝ) < ξ := by linarith
  have hξpos : (0 : ℝ) < ξ := by linarith
  obtain ⟨hLxlo, hLxhi, hLLxlo, hLLxhi, _, _⟩ := phaseEnclosure_WH hξlo hξhi
  have hLxpos : (0 : ℝ) < Real.log ξ := by linarith
  have hLLxpos : (0 : ℝ) < Real.log (Real.log ξ) := by linarith
  obtain ⟨hQp_lo, hQp_hi⟩ := cert_highCurv_QpBounds hξlo hξhi
  obtain ⟨hQpp_lo, hQpp_hi⟩ := cert_highCurv_QppBounds hξlo hξhi
  set u := iteratedLog 3 ξ with hu
  have hDpos : (0 : ℝ) < ξ * Real.log ξ * Real.log (Real.log ξ) := by positivity
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
  · -- `0.0399 < ξ·q̃'(ξ)`: antitonicity of `y ↦ y·q̃'(y)` on `[8·10²⁶, B]`
    have hanti : AntitoneOn (fun y => y * deriv qCore y) (Set.Icc (8e26 : ℝ) B) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
      · intro x hx
        exact (cert_highData_hasDerivAt_slope
          (by linarith [hx.1] : (3.9e6 : ℝ) < x)).continuousAt.continuousWithinAt
      · rw [interior_Icc]
        intro x hx
        exact (cert_highData_hasDerivAt_slope
          (by linarith [hx.1] : (3.9e6 : ℝ) < x)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        exact cert_highData_slopeDeriv_nonpos (le_of_lt hx.1) (by linarith [hx.2])
    have hslope : B * deriv qCore B ≤ ξ * deriv qCore ξ :=
      hanti ⟨hξlo, hξB⟩ ⟨hB8, le_refl B⟩ hξB
    -- endpoint value `B·q̃'(B) = Q̃₄'(u(B))/(logB·log₂B) > 0.0399`
    have hB39 : (3.9e6 : ℝ) < B := by linarith
    have hBpos : (0 : ℝ) < B := by linarith
    obtain ⟨hLBlo, hLBhi, hLLBlo, hLLBhi, _, _⟩ := phaseEnclosure_H46 hBlo hBhi
    have hLBpos : (0 : ℝ) < Real.log B := by linarith
    have hLLBpos : (0 : ℝ) < Real.log (Real.log B) := by linarith
    have hQpB : (10.84 : ℝ) ≤ deriv QrefCore4 (iteratedLog 3 B) := cert_highData_QpB_lb hBlo hBhi
    have hdB : deriv qCore B
        = deriv QrefCore4 (iteratedLog 3 B)
          * (B * Real.log B * Real.log (Real.log B))⁻¹ := by
      rw [cert_deriv_qCore_eq hB39, cert_iteratedLogThreeDeriv]
    have hφB : (0.0399 : ℝ) < B * deriv qCore B := by
      rw [hdB,
        show B * (deriv QrefCore4 (iteratedLog 3 B)
              * (B * Real.log B * Real.log (Real.log B))⁻¹)
          = deriv QrefCore4 (iteratedLog 3 B) / (Real.log B * Real.log (Real.log B)) from by
          field_simp,
        lt_div_iff₀ (by positivity)]
      have hprod : Real.log B * Real.log (Real.log B) ≤ 64.6555 * 4.169074 :=
        mul_le_mul hLBhi hLLBhi hLLBpos.le (by norm_num)
      nlinarith [hQpB, hprod]
    linarith [hslope, hφB]
  · -- `q̃''(ξ) ≤ 0`
    rw [hd2]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hprod : (61.94665 : ℝ) * 4.12627 ≤ Real.log ξ * Real.log (Real.log ξ) :=
      mul_le_mul hLxlo hLLxlo (by norm_num) (by linarith)
    have hP_lo : (200 : ℝ)
        ≤ Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1 := by
      linarith [hprod, hLLxlo]
    have hQpP : (10.80 : ℝ) * 200 ≤ deriv QrefCore4 u
        * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1) :=
      mul_le_mul hQp_lo hP_lo (by norm_num) (by linarith [hQp_lo])
    linarith [hQpP, hQpp_hi]
  · -- `−ξ q̃''(ξ) < 1.0201 q̃'(ξ)`, the curvature bound
    have hstar : deriv QrefCore4 u * (Real.log (Real.log ξ) + 1)
        - deriv (deriv QrefCore4) u
        < 0.0201 * deriv QrefCore4 u * Real.log ξ * Real.log (Real.log ξ) := by
      have hRHSlow : (55 : ℝ)
          ≤ 0.0201 * (deriv QrefCore4 u * (Real.log ξ * Real.log (Real.log ξ))) := by
        have hprod : (10.80 : ℝ) * (61.94665 * 4.12627)
            ≤ deriv QrefCore4 u * (Real.log ξ * Real.log (Real.log ξ)) := by gcongr
        nlinarith [hprod]
      have hLHShigh : deriv QrefCore4 u * (Real.log (Real.log ξ) + 1)
          - deriv (deriv QrefCore4) u ≤ 42.2 := by
        have hprod2 : deriv QrefCore4 u * (Real.log (Real.log ξ) + 1)
            ≤ 10.97 * (4.1703 + 1) := by gcongr
        nlinarith [hprod2, hQpp_lo]
      nlinarith [hLHShigh, hRHSlow]
    have hb : (0 : ℝ) < 0.0201 * deriv QrefCore4 u * Real.log ξ * Real.log (Real.log ξ)
        - (deriv QrefCore4 u * (Real.log (Real.log ξ) + 1) - deriv (deriv QrefCore4) u) := by
      linarith [hstar]
    have hnumpos : (0 : ℝ) < 1.0201 * deriv QrefCore4 u
          * (ξ * Real.log ξ * Real.log (Real.log ξ))
        + ξ * (deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1)) := by
      nlinarith [mul_pos hξpos hb]
    rw [hd1, hd2]
    have hcomb := curvatureComb 1.0201 (deriv QrefCore4 u) (deriv (deriv QrefCore4) u)
      (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1) ξ
      (ξ * Real.log ξ * Real.log (Real.log ξ)) hDpos.ne'
    have hpos : (0 : ℝ) < 1.0201 * (deriv QrefCore4 u / (ξ * Real.log ξ * Real.log (Real.log ξ)))
        + ξ * ((deriv (deriv QrefCore4) u
          - deriv QrefCore4 u
            * (Real.log ξ * Real.log (Real.log ξ) + Real.log (Real.log ξ) + 1))
          / (ξ * Real.log ξ * Real.log (Real.log ξ)) ^ 2) := by
      rw [hcomb]; exact div_pos hnumpos (by positivity)
    linarith [hpos]

end Erdos320
