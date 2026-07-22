import Erdos320.Defs.StoppingDepth
import Erdos320.Lemmas.BackwardReference

/-!
# Breakpoint-coordinate notation for the certificate lemmas

Shared notation used by the **proved** directed-interval certificate lemmas
(`Erdos320/Lemmas/CertLow*.lean`, `CertHigh*.lean`).  For an input scale `N` and
a candidate value `f`, the breakpoint coordinate is `x(f) = N·f/log N`
(paper eq. `data-transform`); the reference functions are evaluated at
`u(f) = log₃ x(f)`.

These definitions are **not** part of the trust boundary — no `axiom`'s
statement mentions them; they are consumed only by proved theorems — so they
live here rather than in `Erdos320/Assumptions.lean`, keeping that file
axioms-only (see the trust-boundary policy in `CLAUDE.md`).
-/

namespace Erdos320

/-- The breakpoint coordinate `x(f) = N₀·f/log N₀` at the low input
`N₀ = 65 659 969 = ⌊e¹⁸⌋` (paper eq. `data-transform` with `N = N₀`). -/
noncomputable def lowBreakpointX (f : ℝ) : ℝ :=
  65659969 * f / Real.log 65659969

/-- The breakpoint coordinate `x(f) = N₁·f/log N₁` at the high input
`N₁ = ⌊e⁶⁵⌋` (paper eq. `data-transform` with `N = N₁`). -/
noncomputable def highBreakpointX (f : ℝ) : ℝ :=
  16948892444103337141417836114 * f / Real.log 16948892444103337141417836114

/-- The reference profile in the breakpoint coordinate, at the *core* level:
`q̃(ξ) = Q̃₄(log₃ ξ)` — the paper's `q_br(x) = Q₄*(log₃ x)`
(eq. `q-breakpoint-coordinate`), with `Q₄*` replaced by the certified core
`Q̃₄`. -/
noncomputable def qCore (ξ : ℝ) : ℝ := QrefCore4 (iteratedLog 3 ξ)

end Erdos320
