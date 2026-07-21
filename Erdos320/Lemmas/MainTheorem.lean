import Erdos320.Lemmas.Main
import Erdos320.Lemmas.Nonconstancy

/-!
# The main theorem (paper `thm:main`)

The capstone: bundling the phase function's four properties (positive,
continuous, endpoint-matched, **nonconstant**) with the uniform asymptotic
```
log S(N) = (N/log N)·(∏_{j=3}^{h(N)} log_j N)·Φ(u_N)·(1 + 1/log₃N + o(1/log₃N)),
```
the `o(1/log₃N)` realized by the explicit error `C/(log₃N·log₄N)` of
`main_asymptotic` (which is stronger than the paper's `o`-form; the paper's
uniformity statement eq. `main-uniformity` is `main_uniformity_tendsto`).

Trust boundary (auditable with `#print axioms erdos320_main`): the four
axioms of `Erdos320/Assumptions.lean` — `lowFiniteInput`,
`fioriKadiriSwidinsky_pi_approx`, `dusart_theta_k3`, `bgmsSTable` — plus
Lean's foundational three (matching the trust boundary reported in the
manuscript's reproducibility section, `sec:reproducibility`).
(`comp:high` is the proved theorem `highFiniteInput`,
`Erdos320/Lemmas/HighFiniteAssembly.lean`; the six directed-interval
certificate evaluations are proved theorems,
`Erdos320/Lemmas/Cert*.lean`.)  On the nonconstancy side
the axiom cone additionally carries the accepted `native_decide`
compiler-trust entries, while the uniformity capstones are kernel-only on the FKS
estimate (consistent with the `native_decide` carve-out in `CLAUDE.md`).
Everything else, i.e. every step of the manuscript's own argument, is
proved.
-/

namespace Erdos320

/-- **Paper `thm:main`.**  There is a positive, continuous, nonconstant
function `Φ` on `[1, e]` with `Φ(1) = Φ(e)` — namely `phasePhi` — such that,
uniformly in the phase coordinate `u_N ∈ [1, e)`,
`log S(N) = (N/log N)·(∏_{j=3}^{h(N)} log_j N)·Φ(u_N)·(1 + 1/log₃N + o(1/log₃N))`;
the `o(1/log₃N)` is witnessed by the explicit bound `C/(log₃N·log₄N)`. -/
theorem erdos320_main :
    -- Φ is continuous on [1, e] …
    ContinuousOn phasePhi (Set.Icc 1 (Real.exp 1))
    -- … positive …
    ∧ (∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), 0 < phasePhi u)
    -- … matches at the endpoints …
    ∧ phasePhi 1 = phasePhi (Real.exp 1)
    -- … and is NOT constant …
    ∧ (¬ ∃ C : ℝ, ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C)
    -- … and the full asymptotic holds with an explicit uniform error:
    ∧ ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ N : ℕ, N₀ ≤ N →
        |Real.log (S N)
            - ((N : ℝ) / Real.log N)
              * ((∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                * phasePhi (phaseCoordinate N)
                * (1 + 1 / iteratedLog 3 (N : ℝ)))|
          ≤ C * ((N : ℝ) / Real.log N)
              * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
              / (iteratedLog 3 (N : ℝ) * iteratedLog 4 (N : ℝ)) :=
  ⟨phasePhi_continuousOn, phasePhi_pos, phasePhi_endpoint,
    phasePhi_nonconstant, main_asymptotic⟩

/-- `thm:main` in the paper's existential phrasing: *there is* a positive,
continuous, nonconstant, endpoint-matched phase function realizing the
asymptotic. -/
theorem erdos320_main_exists :
    ∃ Φ : ℝ → ℝ,
      ContinuousOn Φ (Set.Icc 1 (Real.exp 1))
      ∧ (∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), 0 < Φ u)
      ∧ Φ 1 = Φ (Real.exp 1)
      ∧ (¬ ∃ C : ℝ, ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), Φ u = C)
      ∧ ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ N : ℕ, N₀ ≤ N →
          |Real.log (S N)
              - ((N : ℝ) / Real.log N)
                * ((∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                  * Φ (phaseCoordinate N)
                  * (1 + 1 / iteratedLog 3 (N : ℝ)))|
            ≤ C * ((N : ℝ) / Real.log N)
                * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                / (iteratedLog 3 (N : ℝ) * iteratedLog 4 (N : ℝ)) :=
  ⟨phasePhi, erdos320_main⟩

end Erdos320
