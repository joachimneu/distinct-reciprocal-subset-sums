# `Erdos320/` — the Lean 4 + Mathlib formalization

This directory is the **proof**: the machine-checked formalization of the
manuscript's **Theorem 1.1** on Erdős Problem #320 (the asymptotic number of
distinct reciprocal subset sums). It is one of the repository's two code pieces;
the other is [`../ComputationalCertificates/`](../ComputationalCertificates/),
which holds the finite computations that back this development's finite-input
axioms. See the [top-level `README.md`](../README.md) for the overall division
and the problem statement.

## Where to start

`Main.lean` and `Assumptions.lean` are the two "read-me-to-trust-everything"
files — `Main.lean` is the exact claim, `Assumptions.lean` is everything
assumed:
- **[`Main.lean`](Main.lean)** restates
  Theorem 1.1 in full, pins every object in the statement (`S(N)`, `log_j`,
  `h(N)`, `u_N`) to its definition with `rfl`-checked recap lemmas, and delegates
  all proofs to `Lemmas/`.
- **[`Assumptions.lean`](Assumptions.lean)** contains the numerical values
  produced by the computational certificates, and results reused from the literature.
  It is the only file
  permitted to declare each of these assumptions as an `axiom`.

## Paper ↔ Lean map

Each numbered item of the manuscript, what it establishes, and where it is
realized in the code.

| Paper # | Type (`label`) | What it establishes | Key Lean location(s) |
|---|---|---|---|
| **1.1** | Theorem (`thm:main`) | The main result: `log S(N)` asymptotic with a positive, continuous, **nonconstant** phase `Φ`, uniform in the phase coordinate `u_N` | `Main.lean` `erdos320_theorem_1_1` (+ `_effective`, `_uniform_error`, `_uniformity`); proved via `Lemmas/MainTheorem.lean`, `Lemmas/Main.lean`, `Nonconstancy.lean` |
| **3.1** | Proposition (`prop:large-prime-decomposition`) | Exact large-prime decomposition: reduces `S(N)` to a fibre factor times a product of modular-image sizes `σ(p,m)` over large primes | `LargePrimeDecomposition.lean`, `CollisionLower.lean` |
| **3.2** | Lemma (`lem:average-collision`) | Average collision bound within a prime shell | `AverageCollision.lean` |
| **4.1** | Lemma (`lem:prime-power-splitting`) | Prime-power splitting of the smooth denominator `𝔇_Q(N)` (the consumed inequality forms) | `ShellDecomposition.lean`, `CollisionLower.lean` |
| **4.2** | Proposition (`prop:averaging-relation`) | Asymptotic averaging relation `F(X) = 𝓑(X) + error`: a concave weighted average over smaller scales | `AveragingRelation.lean`, `AveragingUpper.lean`, `AveragingLower.lean` |
| **4.3** | Lemma (`lem:B-slopes`) | `𝓑` is increasing, concave, 1-Lipschitz, with slope `1/m_*(X)` | `BSlopes.lean` |
| **4.4** | Lemma (`lem:elementary-threshold`) | Two-sided bracket for the threshold index `m_*(t)` | `ElementaryThreshold.lean` |
| **4.5** | Lemma (`lem:threshold`) | Threshold estimate: locates `F(X)` in `[1, log₂X]`; additive slow-variation form | `Threshold.lean` |
| **5.1** | Lemma (`lem:exact-recurrence`) | Exact differentiated / integral recurrence for `H̄_r`, valid a.e. | `ExactRecurrence.lean` |
| **5.2** | Lemma (`lem:iteration-endpoint-matching`) | Iteration with endpoint matching: contracts to a limit profile | `IterationContraction.lean` |
| **5.3** | Proposition (`prop:phase`) | Existence of the phase `Φ`: positive, continuous, `Φ(1) = Φ(e)` | `Phase.lean` |
| **6.1** | Lemma (`lem:backward-reference-convergence`) | Convergence of the backward reference functions, with explicit tail | `BackwardReferenceConvergence.lean` |
| **6.2** | Lemma (`lem:backward-stability`) | Backward stability: error propagation of one backward step | `BackwardStability.lean` |
| **7.1** | Lemma (`lem:breakpoint-chords`) | Quantitative chord bounds at a breakpoint (two-sided bound on the forced constant `C`) | `BreakpointChords.lean` |
| **8.1** | Lemma (`lem:explicit-low-averaging`) | Explicit averaging-error bound on the low window | `ExplicitLowAveraging.lean` |
| **8.2** | Corollary (`cor:explicit-high-averaging`) | The same averaging-error bound on the high window | `ExplicitHighAveraging.lean` |
| **8.3** | Corollary (`cor:explicit-high-rho`) | Pointwise smallness of the recurrence error `ρ` at high depth | `ExplicitHighAveraging.lean` |
| **8.4** | Proposition (`prop:constant-phase-backward`) | Backward propagation for a constant phase to a forced value at depth 4 | `ConstantPhaseBackward.lean` |
| **8.5** | Lemma (`comp:low`) | Low finite input: certified `F` + slope/curvature data at `N₀ = ⌊e¹⁸⌋` (the `C < 1.16` side) | axiom `Assumptions.lean` `lowFiniteInput`; sub-certs `CertLow*.lean`; transfer `CertificateTransfer.lean` |
| **8.6** | Lemma (`comp:high`) | High finite input: certified `F` + data at `N₁ = ⌊e⁶⁵⌋` (the `C > 1.17` side) | proved theorem `HighFiniteAssembly.lean` (+ `HighShellGrid*.lean`, `HighAggregate.lean`); sub-certs `CertHigh*.lean` |
| **8.7** | Proposition (`prop:nonconstant`) | Nonconstancy: the incompatible `C < 1.16` vs `C > 1.17` force `Φ` to be nonconstant | `Nonconstancy.lean` |

### Key defined objects

| `label` | Object | Lean location(s) |
|---|---|---|
| `eq:EN-SN-intro` | `𝓔_N`, `S(N)`, `F(N)` | `Defs/Basic.lean` `reciprocalSubsetSumSet`, `S`, `F` |
| `eq:h-def-intro` | `h(N)`, `u_N`, `log_j` | `Defs/StoppingDepth.lean` `stoppingDepth`, `phaseCoordinate`, `iteratedLog` |
| `eq:sigma-def` | `σ(p,m) = \|B_{p,m}\|` | `Defs/ModularImage.lean` `modularImage`, `sigma` |
| `eq:B-def` | `𝓑(X)`, `m_*`, `ρ`, `H̄_r`, `ρ_r` | `Defs/Averaging.lean` `BTerm`, `B`, `mStar`, `rho`, `Hbar`, `rhoDepth` |
| `eq:main` / `-uniform-error` / `-uniformity` | main asymptotic / explicit uniform error / uniformity | `Lemmas/Main.lean` `main_asymptotic`, `main_uniform_error`, `main_uniformity`, `main_uniformity_tendsto` |

## Build

See the [top-level `README.md`](../README.md#build) for the full build and
no-holes checks. In short:

```bash
lake exe cache get                 # fetch prebuilt Mathlib oleans (do this first)
lake build                         # build the whole project
lake env lean Erdos320/Main.lean   # type-check the trusted core, re-emitting its warnings
```
