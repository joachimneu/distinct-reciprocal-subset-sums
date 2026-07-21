import Erdos320.Lemmas.CoreClosedForm
import Erdos320.Lemmas.PhaseEnclosure

/-!
# Certificate `comp:low`, eq. `low-Q4-positive`, proved in Lean

The manuscript's directed-interval certificate asserts `Q̃₄(log₃ w) > 4.79`
throughout the enlarged low window `w ∈ [9 725 449, 10 632 947]`
(`directed_interval_certificate.py`, transcript `> 4.8` for the limit).  Here
that inequality is proved inside Lean: the closed form of
`QrefCore4` (`CoreClosedForm.lean`) is combined with the explicit rational
enclosures of `E₁,E₂,E₃` on the window (`PhaseEnclosure.lean`).  Over the
window `QrefCore4 ≥ 5.007…`, with wide margin over `4.79`.

The theorem `lowQ4PositiveCert` certifies the core-level inequality behind
the paper's display `eq:low-Q4-positive` on exactly that window; the
core-to-limit transfer to the displayed constant `4.789` happens in
`CertificateTransfer.lean`.
-/

namespace Erdos320

/-- **Proved core-level input to `eq:low-Q4-positive`**:
`Q̃₄(log₃ w) > 4.79` for every `w ∈ [9 725 449, 10 632 947]`. -/
theorem lowQ4PositiveCert (w : ℝ) (h1 : (9725449 : ℝ) ≤ w)
    (h2 : w ≤ 10632947) :
    (4.79 : ℝ) < QrefCore4 (iteratedLog 3 w) := by
  have hw39 : (3.9e6 : ℝ) < w := by linarith
  have hu1 : 1 < iteratedLog 3 w := cert_one_lt_iteratedLog_three hw39
  have hu0 : 0 < iteratedLog 3 w := by linarith
  -- phase-coordinate enclosures
  obtain ⟨he1lo, he1hi, he2lo, he2hi, he3⟩ := phaseEnclosure_E_W h1 h2
  obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_W h1 h2
  -- positivity of the three exponential iterates
  have he1pos : 0 < E 1 (iteratedLog 3 w) := E_pos_of_one_le (by omega) _
  have he2pos : 0 < E 2 (iteratedLog 3 w) := E_pos_of_one_le (by omega) _
  have he3pos : 0 < E 3 (iteratedLog 3 w) := E_pos_of_one_le (by omega) _
  rw [QrefCore4_closedForm hu0]
  set e1 := E 1 (iteratedLog 3 w) with he1def
  set e2 := E 2 (iteratedLog 3 w) with he2def
  set e3 := E 3 (iteratedLog 3 w) with he3def
  set u := iteratedLog 3 w with hudef
  -- window bounds on e3 (= w)
  have he3lo : (9725449 : ℝ) ≤ e3 := by rw [he3]; exact h1
  have he3hi : e3 ≤ 10632947 := by rw [he3]; exact h2
  have hden : 0 < e1 ^ 2 * e2 ^ 2 * e3 := by positivity
  rw [lt_div_iff₀ hden]
  -- Dominant balance: `num − 4.79·e₁²e₂²e₃ = (u·e₁ + u − 3.79)·e₁²e₂²e₃
  --   + (e₁e₂ + e₁²e₂ + u·e₁²e₂)·e₃ + Q`, with `Q ≥ −10000`.
  -- The lead factor `u·e₁ + u − 3.79 ≥ 0.07` (since `u(1+e₁) ≥ 1.0218·3.7782 > 3.86`),
  -- times `e₁²e₂²e₃ ≥ 1.9·10¹⁰`, dwarfs everything.
  have hkey : (0.07 : ℝ) ≤ u * e1 + u - 3.79 := by nlinarith [hulo, he1lo]
  have hbig : (1.9e10 : ℝ) ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
    have h : (2.778213 : ℝ) ^ 2 * 16.090256 ^ 2 * 9725449 ≤ e1 ^ 2 * e2 ^ 2 * e3 := by
      gcongr
    nlinarith [h]
  have hlead : (0.07 : ℝ) * (e1 ^ 2 * e2 ^ 2 * e3)
      ≤ (u * e1 + u - 3.79) * (e1 ^ 2 * e2 ^ 2 * e3) :=
    mul_le_mul_of_nonneg_right hkey hden.le
  have hmid : (0 : ℝ) ≤ (e1 * e2 + e1 ^ 2 * e2 + u * e1 ^ 2 * e2) * e3 := by positivity
  -- upper bounds for the `Q` monomials (all with e₃-free, so bounded)
  have hQ : (-10000 : ℝ) ≤
      -1 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2 - u * e1 ^ 2 - u * e1 ^ 2 * e2 ^ 2
        - u * e1 ^ 3 * e2 ^ 2 := by
    have b1 : e1 ^ 2 ≤ 8 := by nlinarith [he1hi, he1pos]
    have b2 : e1 ^ 2 * e2 ^ 2 ≤ 2029 := by
      have h : e1 ^ 2 * e2 ^ 2 ≤ 2.783744 ^ 2 * 16.179468 ^ 2 := by gcongr
      nlinarith [h]
    have b3 : u * e1 ^ 2 ≤ 8 := by nlinarith [huhi, he1hi, he1pos]
    have b4 : u * e1 ^ 2 * e2 ^ 2 ≤ 2078 := by
      have h : u * e1 ^ 2 * e2 ^ 2 ≤ 1.023797 * 2.783744 ^ 2 * 16.179468 ^ 2 := by
        gcongr
      nlinarith [h]
    have b5 : u * e1 ^ 3 * e2 ^ 2 ≤ 5783 := by
      have h : u * e1 ^ 3 * e2 ^ 2 ≤ 1.023797 * 2.783744 ^ 3 * 16.179468 ^ 2 := by
        gcongr
      nlinarith [h]
    linarith [b1, b2, b3, b4, b5]
  nlinarith [hlead, hbig, hmid, hQ]

end Erdos320
