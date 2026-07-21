# `Erdos320/` — the Lean 4 + Mathlib formalization

This directory is the **proof**: the machine-checked formalization of the
manuscript's **Theorem 1.1** on Erdős Problem #320 (the asymptotic number of
distinct reciprocal subset sums). It is one of the repository's two code pieces;
the other is [`../ComputationalCertificates/`](../ComputationalCertificates/),
which holds the finite computations that back this development's finite-input
axioms. See the [top-level `README.md`](../README.md) for the overall division
and the problem statement.

**Lean's kernel is the authority.** Nothing here is treated as a verified
mathematical fact until Lean has checked it; "the paper says so" is a hypothesis
to be discharged, not a citation that settles anything.

## Where to start

- **[`Main.lean`](Main.lean) — the trusted core; read this first.** It restates
  Theorem 1.1 in full, pins every object in the statement (`S(N)`, `log_j`,
  `h(N)`, `u_N`) to its definition with `rfl`-checked recap lemmas, and delegates
  all proofs to `Lemmas/`. One file, one glance: it lets a reader confirm the
  definitions are faithful and the statement proved is the right theorem without
  reading any proof. It is deliberately kept stable and is not edited except on
  explicit request.
- **[`Assumptions.lean`](Assumptions.lean) — the trust boundary.** The only file
  permitted to declare an `axiom` (see below).

`Main.lean` and `Assumptions.lean` are the two "read-me-to-trust-everything"
files: a human gains confidence in the whole mechanization by inspecting only
these two — `Main.lean` is the exact claim, `Assumptions.lean` is everything
assumed. Both are kept deliberately minimal.

## Layout

- **`Main.lean`** — the trusted core (statement restatements + one-line
  invocations of `Lemmas/`; no proofs live here).
- **`Defs/`** — the load-bearing definitions on top of Mathlib. The base module
  `Defs/Basic.lean` defines `reciprocalSubsetSumSet (N) : Finset ℚ` (`= 𝓔_N`),
  `S (N) : ℕ` (`= |𝓔_N|`), and the normalized count `F (N) : ℝ`, plus honestly
  proven basics (`S 0 = 1`, `1 ≤ S N`, `Monotone S`). The rest of `Defs/` adds
  the iterated logarithms, stopping depth `h(N)` / phase coordinate `u_N`, the
  averaging profile `𝓑` and `H̄_r`/`ρ_r`, and the modular images `σ`.
- **`Lemmas/`** — the proof: the analytic development plus the capstone theorems
  in `Lemmas/Main.lean` and `Lemmas/MainTheorem.lean` that `Main.lean` invokes.
- **`Assumptions.lean`** — the trust boundary (see below).

`reciprocalSubsetSumSet`, `S`, and `F` are the definitions the meaning of every
paper-facing theorem rests on; mis-stating them (dropping the `{1,…,N}` range,
the empty-sum contribution `S(0)=1`, or the `ℚ`-valued exactness) could make a
downstream result vacuous while still compiling.

## Trust boundary

`Assumptions.lean` is the single, explicit hole in the wall — the only file
where an unproved fact may be assumed. It currently holds **exactly four
axioms**:

- `lowFiniteInput` — the computer-assisted low finite input `F(⌊e¹⁸⌋)` (a
  ~10¹³-operation enumeration not feasibly reproducible in Lean; backed by
  [`../ComputationalCertificates/`](../ComputationalCertificates/)).
- `fioriKadiriSwidinsky_pi_approx` — the Fiori–Kadiri–Swidinsky explicit
  prime-counting estimate (literature).
- `dusart_theta_k3` — Dusart's explicit Chebyshev bound, `k = 3` row
  (literature).
- `bgmsSTable` — the published BGMS `S(0..83)` table (literature; the matching
  data file lives in `../ComputationalCertificates/`).

Everything downstream must be genuinely proved — no `sorry`, `admit`, `unsafe`,
or hand-declared `axiom` anywhere else. In particular the directed-interval
certificate evaluations (`Cert*.lean`) and the high finite input
`F(⌊e⁶⁵⌋) > 3.2411` (`HighFiniteAssembly.lean`) are proved theorems, not axioms.

Audit any theorem's real dependencies with `#print axioms <thm>`: it must list
only the four axioms above, Lean's `propext`/`Classical.choice`/`Quot.sound`,
and — solely via the `highFiniteInput` cluster (the nonconstancy side) — the
accepted `native_decide` compiler-trust entries. The uniformity-side capstones
carry none and remain kernel-only. Anything else is a leaked hole and a defect.

## Paper ↔ Lean map

Each numbered item of the manuscript, what it establishes, and where it is
realized in the code (cited by file + declaration name — names are stable, line
numbers drift; all declarations are in `namespace Erdos320`). The manuscript
shares one `Section.n` counter across theorems/propositions/lemmas/corollaries
and its computer-assisted lemmas.

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
| **8.5** | Comp. lemma (`comp:low`) | Low finite input: certified `F` + slope/curvature data at `N₀ = ⌊e¹⁸⌋` (the `C < 1.16` side) | axiom `Assumptions.lean` `lowFiniteInput`; sub-certs `CertLow*.lean`; transfer `CertificateTransfer.lean` |
| **8.6** | Comp. lemma (`comp:high`) | High finite input: certified `F` + data at `N₁ = ⌊e⁶⁵⌋` (the `C > 1.17` side) | proved theorem `HighFiniteAssembly.lean` (+ `HighShellGrid*.lean`, `HighAggregate.lean`); sub-certs `CertHigh*.lean` |
| **8.7** | Proposition (`prop:nonconstant`) | Nonconstancy: the incompatible `C < 1.16` vs `C > 1.17` force `Φ` to be nonconstant | `Nonconstancy.lean` |

### Key defined objects

| `label` | Object | Lean location(s) |
|---|---|---|
| `eq:EN-SN-intro` | `𝓔_N`, `S(N)`, `F(N)` | `Defs/Basic.lean` `reciprocalSubsetSumSet`, `S`, `F` |
| `eq:h-def-intro` | `h(N)`, `u_N`, `log_j` | `Defs/StoppingDepth.lean` `stoppingDepth`, `phaseCoordinate`, `iteratedLog` |
| `eq:sigma-def` | `σ(p,m) = |B_{p,m}|` | `Defs/ModularImage.lean` `modularImage`, `sigma` |
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
