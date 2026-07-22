import Erdos320.Lemmas.MainTheorem

/-!
# Theorem 1.1 — the trusted core (read this file first)

This file is the **audit front page** of the `Erdos320` formalization. Its job
is that a reader can, *in one glance and without trusting any proof*, convince
themselves of two things:

1. that the objects named in the theorem (`S(N)`, the iterated logarithm
   `log_j`, the stopping depth `h(N)`, the phase coordinate `u_N`) are
   formalized *faithfully* to the manuscript; and
2. that the statement proved is *exactly* the manuscript's **Theorem 1.1**
   (`\label{thm:main}`).

To keep it readable, **no proofs live here**. Every theorem below is proved by
a one-line invocation of a fully-proved theorem in `Erdos320/Lemmas/`
(`Main.lean`, `MainTheorem.lean`). Lean checks that the statement restated here
is definitionally the one proved there, so the delegation cannot hide a
mismatch. For where each *paper* item is realized in the code, see
`Erdos320/README.md`.

## Paper Theorem 1.1 (`\label{thm:main}`)

> There is a positive, continuous, nonconstant function `Φ : [1, e] → (0, ∞)`
> satisfying `Φ(1) = Φ(e)` such that, as `N → ∞`, uniformly in `u_N ∈ [1, e)`,
> ```
> log S(N) = (N / log N) · (∏_{j=3}^{h(N)} log_j N) · Φ(u_N)
>            · (1 + 1/log₃N + O(1/(log₃N·log₄N))).          (eq:main)
> ```
> The `O`-constant is absolute and uniform in `u_N`. More explicitly, if we
> write `𝓜(N) = (N/log N)·∏_{j=3}^{h(N)} log_j N`, there are constants
> `C_asym, N_asym > 0` such that, for every integer `N ≥ N_asym`,
> ```
> |log S(N)/(𝓜(N)·Φ(u_N)) − 1 − 1/log₃N|
>     ≤ C_asym/(log₃N·log₄N).                    (eq:main-uniform-error)
> ```
> In particular, our estimate implies the following uniform little-`o` form:
> ```
> lim_{T→∞} sup_{N ≥ T} log₃N · |log S(N)/(𝓜(N)·Φ(u_N)) − 1 − 1/log₃N|
>     = 0.                                          (eq:main-uniformity)
> ```

## The objects in the statement

The four central objects, with their exact Lean definitions (each pinned
below by a `rfl`-checked `example`, so this documentation cannot drift from the
real definitions):

* `S N = |𝓔_N|`, where `𝓔_N = { ∑_{n ∈ A} 1/n : A ⊆ {1,…,N} } ⊆ ℚ` is the set
  of distinct reciprocal subset sums (empty sum `0` included, so `S 0 = 1`).
  Defined in `Erdos320/Defs/Basic.lean`.
* `iteratedLog j x = log_j x`, the `j`-fold natural logarithm (`log_0 x = x`,
  `log_{j+1} x = log(log_j x)`). Defined in `Erdos320/Defs/StoppingDepth.lean`.
* `stoppingDepth N = h(N) = max{ j : 1 ≤ log_k N for all k ≤ j }`, the paper's
  `max{ j ≥ 3 : log_k N ≥ 1 for every 3 ≤ k ≤ j }` (`eq:h-def-intro`). The
  quantification is downward (`∀ k ≤ j`) precisely so the iteration stops at
  its *first* crossing below `1`: Mathlib's total `Real.log x = Real.log |x|`
  cannot make the predicate "resurrect" at junk depths past that crossing —
  see the note in `Erdos320/Defs/StoppingDepth.lean`.
* `phaseCoordinate N = u_N = log_{h(N)} N ∈ [1, e)`, the phase coordinate.

The phase `Φ` itself is *existentially quantified* in the headline statement
(`erdos320_theorem_1_1`), so trusting the statement requires trusting only the
four objects above. The concrete witness is `phasePhi`
(`Erdos320/Lemmas/Phase.lean`), and `erdos320_theorem_1_1_effective` exposes it
together with an explicit (effective) error bound.
-/

namespace Erdos320

/-! ## Definition recap (machine-checked)

Each `example` below re-displays a statement object as its fully-expanded
definition and is closed by `rfl`. This is what makes the recap above trustworthy
rather than mere prose. -/

/-- `S N` is the cardinality of the set of reciprocal subset sums. -/
example (N : ℕ) :
    S N = ((Finset.Icc 1 N).powerset.image
      fun A : Finset ℕ => ∑ n ∈ A, (1 : ℚ) / (n : ℚ)).card := rfl

/-- `log_0 x = x`. -/
example (x : ℝ) : iteratedLog 0 x = x := rfl

/-- `log_{j+1} x = log (log_j x)`. -/
example (j : ℕ) (x : ℝ) : iteratedLog (j + 1) x = Real.log (iteratedLog j x) := rfl

/-- `h(N)` is the greatest depth at which every iterated log down to it is `≥ 1`. -/
example (N : ℕ) :
    stoppingDepth N
      = Nat.findGreatest (fun j => ∀ k ≤ j, 1 ≤ iteratedLog k (N : ℝ)) N := rfl

/-- `u_N = log_{h(N)} N`. -/
example (N : ℕ) : phaseCoordinate N = iteratedLog (stoppingDepth N) (N : ℝ) := rfl

/-! ## Theorem 1.1 -/

/-- **Erdős Problem #320 — paper Theorem 1.1 (`thm:main`).**
There is a positive, continuous, nonconstant function `Φ : [1, e] → (0, ∞)`
with `Φ(1) = Φ(e)` such that, uniformly in the phase coordinate
`u_N ∈ [1, e)`,
```
log S(N) = (N/log N)·(∏_{j=3}^{h(N)} log_j N)·Φ(u_N)
           ·(1 + 1/log₃N + O(1/(log₃N·log₄N))).
```
The inequality below realizes the `O(1/(log₃N·log₄N))` remainder in the
explicit-constant shape of the paper's `eq:main-uniform-error` (constants
`C_asym`, `N_asym`), with the error measured against `𝓜(N)` instead of
`𝓜(N)·Φ(u_N)` — equivalent up to the bounded positive factor `Φ(u_N)`,
absorbed into `C`. See `erdos320_theorem_1_1_effective` for the named phase,
`erdos320_theorem_1_1_uniform_error` for the paper's `𝓜(N)·Φ(u_N)`-normalized
display `eq:main-uniform-error` verbatim, and `erdos320_theorem_1_1_uniformity`
for the little-`o` consequence `eq:main-uniformity`.

Proved in `Erdos320/Lemmas/MainTheorem.lean` as `erdos320_main_exists`. -/
theorem erdos320_theorem_1_1 :
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
  erdos320_main_exists

/-- **Theorem 1.1, effective form.** The same statement with the phase named
explicitly (`Φ = phasePhi`) and the remainder in the concrete uniform shape
`C·𝓜(N)/(log₃N·log₄N)` of the paper's explicit-constant form
`eq:main-uniform-error` (constants `C_asym`, `N_asym`). Proved as
`erdos320_main`. -/
theorem erdos320_theorem_1_1_effective :
    ContinuousOn phasePhi (Set.Icc 1 (Real.exp 1))
    ∧ (∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), 0 < phasePhi u)
    ∧ phasePhi 1 = phasePhi (Real.exp 1)
    ∧ (¬ ∃ C : ℝ, ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp 1), phasePhi u = C)
    ∧ ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ N : ℕ, N₀ ≤ N →
        |Real.log (S N)
            - ((N : ℝ) / Real.log N)
              * ((∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                * phasePhi (phaseCoordinate N)
                * (1 + 1 / iteratedLog 3 (N : ℝ)))|
          ≤ C * ((N : ℝ) / Real.log N)
              * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
              / (iteratedLog 3 (N : ℝ) * iteratedLog 4 (N : ℝ)) :=
  erdos320_main

/-- **Theorem 1.1, normalized explicit error (`eq:main-uniform-error`).** The
paper's explicit-constant display, verbatim: with
`𝓜(N) = (N/log N)·∏_{j=3}^{h(N)} log_j N`, there are constants
`C_asym, N_asym > 0` such that for every integer `N ≥ N_asym`,
```
|log S(N)/(𝓜(N)·Φ(u_N)) − 1 − 1/log₃N| ≤ C_asym/(log₃N·log₄N),
```
with the concrete phase `Φ = phasePhi`. Proved in `Erdos320/Lemmas/Main.lean`
as `main_uniform_error`. -/
theorem erdos320_theorem_1_1_uniform_error :
    ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧
      ∀ N : ℕ, N₀ ≤ N →
        |Real.log (S N)
            / (((N : ℝ) / Real.log N)
              * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
              * phasePhi (phaseCoordinate N))
          - 1 - 1 / iteratedLog 3 (N : ℝ)|
        ≤ C / (iteratedLog 3 (N : ℝ) * iteratedLog 4 (N : ℝ)) :=
  main_uniform_error

/-- **Theorem 1.1, uniformity (`eq:main-uniformity`), `Tendsto` form.** The
paper's uniform little-`o` form — stated in the manuscript as a consequence of
`eq:main-uniform-error` (= `erdos320_theorem_1_1_uniform_error` above): the
`log₃N`-scaled normalized error tends to `0` as `N → ∞`. Proved as
`main_uniformity_tendsto`. -/
theorem erdos320_theorem_1_1_uniformity :
    Filter.Tendsto (fun N : ℕ =>
        iteratedLog 3 (N : ℝ)
          * |Real.log (S N)
              / (((N : ℝ) / Real.log N)
                * (∏ j ∈ Finset.Icc 3 (stoppingDepth N), iteratedLog j (N : ℝ))
                * phasePhi (phaseCoordinate N))
            - 1 - 1 / iteratedLog 3 (N : ℝ)|)
      Filter.atTop (nhds 0) :=
  main_uniformity_tendsto

end Erdos320
