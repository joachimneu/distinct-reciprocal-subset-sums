import Erdos320.Lemmas.CoreClosedForm
import Erdos320.Lemmas.PhaseEnclosure

/-!
# Certificate `comp:low`, eq. `low-slope-margin`, proved in Lean

The manuscript's directed-interval certificate asserts the slope-margin bound
`x(f)·q̃'(x(f)) = Q̃₃(u(f)) / log x(f) > 0.1389` throughout the wide low input
range `f ∈ [2.78, 2.80]`, where `x(f) = 65 659 969·f / log 65 659 969` is the
low breakpoint coordinate and `u(f) = log₃ x(f)`
(transcript `> 0.1390`).  Here the
equivalent core-level form
`0.1389 · log x(f) < Q̃₃(log₃ x(f))`
is proved inside Lean, by the same technique as `CertLowQ4Positive.lean`: the closed form
of `Q̃₃` (`CoreClosedForm.lean`) combined with the explicit rational enclosures
of `E₁,E₂,E₃` on the certified window (`PhaseEnclosure.lean`).

For `f ∈ [2.78, 2.80]` the breakpoint coordinate lands in
`x(f) ∈ [10 140 761, 10 213 830] ⊆ [10 140 000, 10 214 000]`, the sharp phase
window `S`.  There `log x(f) ≤ 16.13927`, so the left side is at most
`0.1389·16.13927 = 2.24174…`; while the right side satisfies
`Q̃₃(log₃ x(f)) ≥ 2.245` (numerically `≈ 2.2490`), a comfortable `~0.007`
margin.  We take the **grouped-form** route: `Q̃₃` is rewritten as
`(1+u) + 1/E₁ − (1+u)/E₂ − 1/(E₁²E₂) + P/(E₁³E₂²E₃)` with `P ≥ 0`, and the
leading part is bounded termwise via reciprocal enclosures.

The theorem `lowSlopeMarginCert` certifies the core-level slope margin behind
the paper's display `eq:low-slope-margin` (whose stated constant is the weakened
`> 0.13889`, implied by the `0.1389` proved here), on exactly the paper's input
range `f ∈ [2.78, 2.80]`.
-/

namespace Erdos320

set_option maxHeartbeats 1000000 in
/-- **Proved core-level input to `eq:low-slope-margin`**:
`0.1389 · log x(f) < Q̃₃(log₃ x(f))` for every `f ∈ [2.78, 2.80]`, where
`x(f) = 65 659 969·f / log 65 659 969`. -/
theorem lowSlopeMarginCert (f : ℝ) (h1 : (2.78 : ℝ) ≤ f) (h2 : f ≤ 2.80) :
    0.1389 * Real.log (lowBreakpointX f)
      < QrefCore3 (iteratedLog 3 (lowBreakpointX f)) := by
  -- `log N₀ ∈ [17.9999, 18.0001]` and its positivity
  obtain ⟨hLlo, hLhi⟩ := cert_log_N0_bounds
  have hLpos : (0 : ℝ) < Real.log 65659969 := by linarith
  -- window bounds on the breakpoint coordinate `ξ = x(f)`
  have hξlo : (10140000 : ℝ) ≤ lowBreakpointX f := by
    rw [lowBreakpointX, le_div_iff₀ hLpos]; nlinarith [h1, hLhi]
  have hξhi : lowBreakpointX f ≤ 10214000 := by
    rw [lowBreakpointX, div_le_iff₀ hLpos]; nlinarith [h2, hLlo]
  set ξ := lowBreakpointX f with hξdef
  -- `log₃ ξ > 1 > 0`
  have hu1 : 1 < iteratedLog 3 ξ := cert_one_lt_iteratedLog_three (by linarith)
  have hu0 : 0 < iteratedLog 3 ξ := by linarith
  -- left side: `0.1389 · log ξ ≤ 2.2418` (since `log ξ ≤ 16.13927`)
  obtain ⟨_, hloghi, _, _, _, _⟩ := phaseEnclosure_S hξlo hξhi
  have hLHS : 0.1389 * Real.log ξ ≤ 2.2418 := by nlinarith [hloghi]
  -- right side: `Q̃₃(log₃ ξ) ≥ 2.245`
  have hRHS : (2.245 : ℝ) ≤ QrefCore3 (iteratedLog 3 ξ) := by
    -- phase-coordinate enclosures on the sharp window `S`
    obtain ⟨he1lo, he1hi, he2lo, he2hi, _he3⟩ := phaseEnclosure_E_S hξlo hξhi
    obtain ⟨_, _, _, _, hulo, huhi⟩ := phaseEnclosure_S hξlo hξhi
    have he1pos : 0 < E 1 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
    have he2pos : 0 < E 2 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
    have he3pos : 0 < E 3 (iteratedLog 3 ξ) := E_pos_of_one_le (by omega) _
    have e1ne : E 1 (iteratedLog 3 ξ) ≠ 0 := he1pos.ne'
    have e2ne : E 2 (iteratedLog 3 ξ) ≠ 0 := he2pos.ne'
    have e3ne : E 3 (iteratedLog 3 ξ) ≠ 0 := he3pos.ne'
    -- grouped closed form `Q̃₃ = M + P/(E₁³E₂²E₃)`, `M` decoupled, `P` the
    -- `E₃`-free remainder (verified exactly against the 20-term closed form)
    have hgroup : QrefCore3 (iteratedLog 3 ξ)
        = ((1 : ℝ) + iteratedLog 3 ξ) + 1 / E 1 (iteratedLog 3 ξ)
            - ((1 : ℝ) + iteratedLog 3 ξ) / E 2 (iteratedLog 3 ξ)
            - 1 / (E 1 (iteratedLog 3 ξ) ^ 2 * E 2 (iteratedLog 3 ξ))
          + (2 + 2 * E 1 (iteratedLog 3 ξ)
              + E 1 (iteratedLog 3 ξ) * E 2 (iteratedLog 3 ξ)
              - E 1 (iteratedLog 3 ξ) ^ 2
              - E 1 (iteratedLog 3 ξ) ^ 2 * E 2 (iteratedLog 3 ξ) ^ 2
              + 2 * E 1 (iteratedLog 3 ξ) ^ 3
              + E 1 (iteratedLog 3 ξ) ^ 3 * E 2 (iteratedLog 3 ξ)
              - E 1 (iteratedLog 3 ξ) ^ 3 * E 2 (iteratedLog 3 ξ) ^ 2
              + E 1 (iteratedLog 3 ξ) ^ 3 * E 2 (iteratedLog 3 ξ) ^ 3
              + 2 * iteratedLog 3 ξ * E 1 (iteratedLog 3 ξ) ^ 3
              + iteratedLog 3 ξ * E 1 (iteratedLog 3 ξ) ^ 3 * E 2 (iteratedLog 3 ξ)
              - iteratedLog 3 ξ * E 1 (iteratedLog 3 ξ) ^ 3 * E 2 (iteratedLog 3 ξ) ^ 2
              + iteratedLog 3 ξ * E 1 (iteratedLog 3 ξ) ^ 3 * E 2 (iteratedLog 3 ξ) ^ 3
              + iteratedLog 3 ξ * E 1 (iteratedLog 3 ξ) ^ 4 * E 2 (iteratedLog 3 ξ) ^ 3)
            / (E 1 (iteratedLog 3 ξ) ^ 3 * E 2 (iteratedLog 3 ξ) ^ 2
                * E 3 (iteratedLog 3 ξ)) := by
      rw [QrefCore3_closedForm hu0]; field_simp; ring
    rw [hgroup]
    set e1 := E 1 (iteratedLog 3 ξ) with he1def
    set e2 := E 2 (iteratedLog 3 ξ) with he2def
    set e3 := E 3 (iteratedLog 3 ξ) with he3def
    set u := iteratedLog 3 ξ with hudef
    -- reciprocal enclosures for the decoupled leading part `M`
    have hr1 : (0.3595497 : ℝ) ≤ 1 / e1 := by
      rw [le_div_iff₀ he1pos]; nlinarith [he1hi]
    have hr2 : ((1 : ℝ) + u) / e2 ≤ 0.1253970 := by
      rw [div_le_iff₀ he2pos]; nlinarith [huhi, he2lo]
    have hd3 : (2.780804 : ℝ) ^ 2 * 16.131998 ≤ e1 ^ 2 * e2 := by gcongr
    have hr3 : 1 / (e1 ^ 2 * e2) ≤ 0.0080163 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hd3]
    -- the `E₃`-free remainder `P` is nonnegative (dominant positive monomials
    -- outweigh the four negative ones by `~3·10⁵`)
    have hP : (0 : ℝ) ≤ 2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
        + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3 := by
      have b1 : (2.780804 : ℝ) ^ 3 * 16.131998 ^ 3 ≤ e1 ^ 3 * e2 ^ 3 := by gcongr
      have b2 : (1.02274 : ℝ) * 2.780804 ^ 4 * 16.131998 ^ 3
          ≤ u * e1 ^ 4 * e2 ^ 3 := by gcongr
      have n1 : e1 ^ 2 ≤ (2.781256 : ℝ) ^ 2 := by gcongr
      have n2 : e1 ^ 2 * e2 ^ 2 ≤ (2.781256 : ℝ) ^ 2 * 16.13927 ^ 2 := by gcongr
      have n3 : e1 ^ 3 * e2 ^ 2 ≤ (2.781256 : ℝ) ^ 3 * 16.13927 ^ 2 := by gcongr
      have n4 : u * e1 ^ 3 * e2 ^ 2
          ≤ (1.022903 : ℝ) * 2.781256 ^ 3 * 16.13927 ^ 2 := by gcongr
      have hpos : (0 : ℝ) ≤ 2 * e1 + e1 * e2 + 2 * e1 ^ 3 + e1 ^ 3 * e2
          + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 + u * e1 ^ 3 * e2 ^ 3 := by positivity
      nlinarith [b1, b2, n1, n2, n3, n4, hpos]
    have hden : (0 : ℝ) < e1 ^ 3 * e2 ^ 2 * e3 := by positivity
    have hPden : (0 : ℝ) ≤ (2 + 2 * e1 + e1 * e2 - e1 ^ 2 - e1 ^ 2 * e2 ^ 2
        + 2 * e1 ^ 3 + e1 ^ 3 * e2 - e1 ^ 3 * e2 ^ 2 + e1 ^ 3 * e2 ^ 3
        + 2 * u * e1 ^ 3 + u * e1 ^ 3 * e2 - u * e1 ^ 3 * e2 ^ 2
        + u * e1 ^ 3 * e2 ^ 3 + u * e1 ^ 4 * e2 ^ 3) / (e1 ^ 3 * e2 ^ 2 * e3) :=
      div_nonneg hP hden.le
    linarith [hr1, hr2, hr3, hulo, hPden]
  linarith [hLHS, hRHS]

end Erdos320
