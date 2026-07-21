import Erdos320.Defs.Basic
import Erdos320.Defs.PrimeCounting
import Erdos320.Defs.StoppingDepth
import Erdos320.Lemmas.BackwardReference

/-!
# Assumptions — the trust boundary of the formalization

This file collects **every** statement the formalization takes on faith rather
than proving inside Lean. Two kinds of input belong here, and nothing else:

* **External results** cited from the literature — e.g. explicit
  prime-number / Chebyshev estimates — in the explicit quantitative form the
  manuscript uses, which Mathlib does not (yet) provide; and
* **Computer-assisted lemmas** whose proof is a finite computation carried out
  by an external certificate program, not by the manuscript's prose and not
  reproducible inside Lean at feasible cost (the relevant `S(N)` are far too
  large to enumerate).

Each `axiom` documents **(a)** where it is used in the manuscript (labels are
the `\label{…}` names in the TeX source) and **(b)** where it comes from — a
literature reference, or a certificate program/transcript whose repo-tracked
copy lives in `ComputationalCertificates/` (see that folder's `README.md` for
provenance and hashes).

## Policy (enforced; see `CLAUDE.md`)

`axiom` may appear in **this file and nowhere else** under `Erdos320/`. No file
— including this one — may use `sorry`, `admit`, or `unsafe`. Consequently the
real dependency set of any theorem is auditable with `#print axioms`: it must
list only the axioms declared here, plus Lean's own foundational three
(`propext`, `Classical.choice`, `Quot.sound`) — and, on the nonconstancy side
only (via the `highFiniteInput` cluster), the accepted `native_decide`
compiler-trust entries; the uniformity capstones carry none. Anything else
means a hole leaked in.

**Do not** add an axiom for a step of the *manuscript's own argument*: the goal
of this repository is to check that reasoning in Lean, so axiomatizing it would
defeat the purpose. Axioms here are only for inputs the manuscript itself
imports from outside or defers to a machine.

## Current trust boundary: exactly four axioms

`#print axioms erdos320_main` lists exactly these four axioms plus Lean's
foundational three (together with the accepted `native_decide` compiler-trust
entries contributed by the nonconstancy-side `highFiniteInput` cluster; the
uniformity capstones carry none):

1. `lowFiniteInput`  — the certified `F(⌊e¹⁸⌋)` enclosure (`comp:low`);
2. `fioriKadiriSwidinsky_pi_approx` — the explicit prime-counting estimate
   (`FKS-pi`);
3. `dusart_theta_k3` — Dusart's explicit Chebyshev `ϑ` bound, Theorem 4.2 `k = 3`
   row (`|ϑ(t)−t| ≤ t/(log t)³`, `t ≥ 89 967 803`); the consumed
   `0.006788·t/log t` form (`theta-explicit`) is the *proved theorem*
   `dusart_theta_approx`, not an axiom;
4. `bgmsSTable` — the Bettin–Grenié–Molteni–Sanna exact values `S(0),…,S(83)`.

All four are genuine *external* inputs: (1) is a finite enumeration certificate
(`comp:low`), (2)–(3) are published explicit analytic number-theory estimates,
and (4) is a published exact-value table.  The two **finite-input
certificates** differ in status: `comp:low` is a program-transcript axiom
(`lowFiniteInput`; the ~10¹³-operation enumeration is not feasibly reproducible
in Lean), whereas `comp:high` (`F(⌊e⁶⁵⌋) > 3.2411`) is the **proved theorem**
`highFiniteInput` (`Erdos320/Lemmas/HighFiniteAssembly.lean`), resting only on
`bgmsSTable` + `dusart_theta_k3` + Lean-checked reasoning — the high input's
trust surface is those two citable literature facts, not a certificate
program.

The **six directed-interval certificate lemmas** the manuscript computes with
`directed_interval_certificate.py` (the value/slope/curvature bounds on the
elementary reference core `Q̃₄ = QrefCore4`, `Q̃₃ = QrefCore3` of eq.
`reference-core`) are likewise **proved theorems**: they follow in Lean from
the closed form of the core (`CoreClosedForm.lean`) and explicit rational
`exp`/`log` enclosures (`PhaseEnclosure.lean`, `PhaseEnclosureHigh.lean`); see
`Erdos320/Lemmas/CertLow*.lean`, `CertHigh*.lean`.  (The core→limit transfer via
the proved tail bound `R7-tail`, and the derived profile-distance /
breakpoint-window claims, are proved, not axiomatized.)
-/

namespace Erdos320

/-- **Computer-assisted lemma (low finite input).**
The certified two-sided enclosure of the normalized count `F` at
`N₀ = 65659969 = ⌊e¹⁸⌋`.

**Where used in the manuscript:**
§8 "Finite inputs proving nonconstancy", subsection "The low finite input",
Computational Lemma `comp:low` / eq. `low-F`.  It feeds the right-hand chord
inequality of §8 "The contradiction" that bounds the hypothetical constant
phase `C` from above (`C < 1.16`).

**Reference / citation.**  This is a *computer-assisted* result with **no
external-paper input** — it is not cited from the literature but recomputed by
the manuscript's own certificate program.  Source: the exact large-prime
modular-image enumeration `pilot_mod_images.cpp` (mode `--certify-low`) with
directed fixed-point logarithms, described in the manuscript's
"Implementation and reproducibility of the finite certificates" section
(`sec:reproducibility`); archived transcript `low_fixed_certificate.out`
(program, transcript, and certificate documentation are repo-tracked in
`ComputationalCertificates/` — see that folder's `README.md`).  The transcript's
certified
enclosure is `CERT F_interval=[2.7872472015,2.7917955118]` (transcript line 7;
integer bounds and the directed-log proof in `LOW_FIXED_CERTIFICATE.md`), which
strictly implies the outward-rounded endpoints assumed here — themselves
digit-for-digit the manuscript's eq. `low-F` in Computational Lemma `comp:low`.
The transcript's headline conclusion `2.78 < F(N₀) < 2.80` is the coarser
public form of the same enclosure. -/
axiom lowFiniteInput :
    (2.78724720 : ℝ) < F 65659969 ∧ F 65659969 < 2.79179560

/-
**High finite input (`comp:high`) — a proved theorem, not an axiom.**

The certified lower bound `3.2411 < F(⌊e⁶⁵⌋)` (`N₁ = 16948892444103337141417836114`)
is **proved in Lean**:

    Erdos320.highFiniteInput      (alias of `highFiniteInput_proof`)
    Erdos320/Lemmas/HighFiniteAssembly.lean

Its trust boundary is exactly the two *citable published literature* inputs
below — the BGMS exact-value table (`bgmsSTable`) and Dusart's explicit Chebyshev
bound (`dusart_theta_k3`, consumed via the derived theorem
`dusart_theta_approx`) — plus Lean-checked reasoning (the large-prime
decomposition `prod_sigma_le_S`, the average-collision lemma, the 35 doubling
identities `S(n)=2S(n-1)`, the tight per-shell collision ledger over `m ≤ 154`,
and one aggregate block over `155 ≤ m ≤ 10⁶`).  Its trust thus rests on two
named theorems from the literature rather than on a certificate program.

`highFiniteInput` feeds the left-hand chord inequality of §8 "The contradiction"
(`C > 1.17`); together with `lowFiniteInput` (`C < 1.16`) it proves `Φ` is not
constant.
-/

/-- **External literature input (explicit prime-counting estimate).**
For every `t ≥ 2`,
`|π(t) − Li(t)| ≤ 9.2211·t·√(log t)·exp(−0.8476·√(log t))`.

**Where used in the manuscript:**
introduced in §4 "A concave averaging relation" as eq. `FKS-pi`; it drives the
shell-count estimates in `prop:averaging-relation`, the explicit range of
`lem:elementary-threshold`, and the explicit averaging-error bounds of
`lem:explicit-low-averaging` / `cor:explicit-high-averaging`, and is reused for
the endpoint prime-count errors in §8.

**Reference / citation.**  This is **Corollary 22** of
A. Fiori, H. Kadiri, J. Swidinsky, *Sharper bounds for the error term in the
Prime Number Theorem*, **Research in Number Theory 9 (2023), no. 3, Paper
No. 63** (`\cite{FioriKadiriSwidinsky}`; the manuscript writes "we use
Corollary~22 of Fiori--Kadiri--Swidinsky"), arXiv:2206.12557.  The exact form
assumed here — coefficient `9.2211`, exponent `−0.8476`, all `x ≥ 2`, `≤` — is
FKS's own statement of the result in their abstract and eq. (3) (p. 2 of the
arXiv version); the display (43) inside Corollary 22 itself (p. 13) carries the
sharper exponent `−0.84768363`, which implies this form.  FKS define
`Li(x) = ∫_2^x dt/log t` (§1.1 Notation, p. 2), matching this project's `Li`.
Not available in Mathlib, which has no explicit-error prime number theorem
of this `e^{−c√log t}` strength. -/
axiom fioriKadiriSwidinsky_pi_approx (t : ℝ) (ht : 2 ≤ t) :
    |(primePi t : ℝ) - Li t| ≤
      9.2211 * t * Real.sqrt (Real.log t) *
        Real.exp (-0.8476 * Real.sqrt (Real.log t))

/-- **External literature input (explicit Chebyshev `ϑ` estimate — Dusart's
`k = 3` bound, verbatim).**
`|ϑ(t) − t| ≤ t / (log t)³` for every `t ≥ 89 967 803`.

**Where used in the manuscript:** it underlies eq. `theta-explicit` (§8), which
supplies the lower prime counts `π(N₁/m) − π(N₁/(m+1))` in the `comp:high`
finite-input argument.  The manuscript states this `k = 3`
estimate and then derives the weaker `0.006788·t/log t` form actually consumed
by the ledger — that derivation is done here in Lean as `dusart_theta_approx`
below (the manuscript's own one-line step, so it is not axiomatized).

**Reference / citation.**  This is **Theorem 4.2, the `k = 3` row**
(`η₃ = 1`, `x₃ = 89 967 803`) of P. Dusart, *Explicit estimates of some
functions over primes*, **The Ramanujan Journal 45 (2018), 227–251**
(`\cite{Dusart}`; in the 2010 preprint arXiv:1002.0442 the same table is
**Theorem 5.2** with the identical `k = 3` row), DOI
10.1007/s11139-016-9839-4 (p. 237).  Dusart states the strict inequality
`|ϑ(x) − x| < x/(ln x)³`; we assume only the weaker `≤`.  Not available in
Mathlib. -/
axiom dusart_theta_k3 (t : ℝ) (ht : (89967803 : ℝ) ≤ t) :
    |chebyshevTheta t - t| ≤ t / (Real.log t) ^ 3

-- The consumed weaker form `|ϑ(t) − t| ≤ 0.006788·t/log t` (`t ≥ 89 967 803`,
-- the manuscript's eq. `theta-explicit`) is NOT an axiom: it is the *proved
-- theorem* `Erdos320.dusart_theta_approx` in `Erdos320/Lemmas/ShellCountDusart.lean`,
-- derived from `dusart_theta_k3` above by the paper's own one-line step
-- (`t ≥ 89 967 803 > e¹⁸ ⇒ log t ≥ 18 ⇒ 1/(log t)² ≤ 1/324 < 0.006788`).
-- Derived theorems live outside this file (see the "Policy" note above): this
-- trust-boundary file holds axioms only.

/-- The exact values `S(0), …, S(83)` computed by Bettin–Grenié–Molteni–Sanna
(BGMS Table 2). `bgmsTable[m]` is their value of `|𝓔_m| = S m`. -/
def bgmsTable : List ℕ :=
  [1, 2, 4, 8, 16, 32, 52, 104, 208, 416, 832, 1664, 1856, 3712, 7424, 9664,
   19328, 38656, 59264, 118528, 126976, 224128, 448256, 896512, 936832,
   1873664, 3747328, 7494656, 7771136, 15542272, 15886336, 31772672, 63545344,
   112064512, 224129024, 231010304, 237031424, 474062848, 948125696,
   1896251392, 1928593408, 3857186816, 3925999616, 7851999232, 12445024256,
   12606504960, 25213009920, 50426019840, 51334348800, 102668697600,
   205337395200, 410674790400, 570733363200, 1141466726400, 1721081528320,
   1751601381376, 1767017021440, 3534034042880, 7068068085760, 14136136171520,
   14245758500864, 28491517001728, 56983034003456, 57494604873728,
   114989209747456, 137824242237440, 139033409748992, 278066819497984,
   522131016253440, 1044262032506880, 1051387483914240, 2102774967828480,
   2116809947873280, 4233619895746560, 8467239791493120, 10638462277386240,
   17372520791408640, 17522758873251840, 17647454272880640, 35294908545761280,
   35499851152097280, 70999702304194560, 141999404608389120,
   283998809216778240]

/-- **External literature input (BGMS exact subset-sum-image counts).**
`S m = |𝓔_m|` equals the tabulated value for every `m ≤ 83`.

**Where used in the manuscript:** `comp:high` (§8) — "we use only the tabulated
exact values `S(m)` for `m ≤ 83`"; the base of the `S(m)`, `m ≤ 154`, lower
bounds (extended by the 35 proved doubling identities) that drive the high
finite input.

**Reference / citation.**  S. Bettin, L. Grenié, G. Molteni, C. Sanna,
*A lower bound for the number of Egyptian fractions*, **Mathematics of
Computation (2026)**, DOI 10.1090/mcom/4190 (arXiv:2509.10030) (`\cite{BGMS}`),
**Table 2** (p. 11 of
the arXiv version; `N = 0, …, 154`, including the printed `N = 0` row
`|E_0| = 1`, so `S(0) = 1` is BGMS's own convention, eq. (1) + `E_0 := {0}`).
Their `E_N`, the varying-target image count over denominators `≤ N`, is exactly
this project's `S N`.  The `bgmsTable` literal above is verified value-by-value
(all 84 entries) against both the paper's Table 2 and the SHA-256-pinned
`S_table_0_83.txt` in `ComputationalCertificates/`. -/
axiom bgmsSTable (m : ℕ) (hm : m ≤ 83) : S m = bgmsTable.getD m 0

/-! ### The certified interval evaluations of the reference core (comp:low, comp:high)

Shared notation for the statements below (paper eq. `data-transform`):
for an input scale `N` and a candidate value `f`, the breakpoint coordinate
is `x(f) = N·f/log N`; the reference functions are evaluated at
`u(f) = log₃ x(f)`. -/

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

/- **The six directed-interval certificate lemmas** (eqs.
`low-slope-match`, `low-slope-margin`, `low-curvature`, `low-Q4-positive`,
`slope-matched-monotonicity`/`high-F`, `high-data`) are **proved in Lean**,
not assumed: all six — the three low-window ones (`lowQ4PositiveCert`,
`lowSlopeMarginCert`, `lowCurvatureCert`) and the three that additionally
need a monotonicity-of-the-candidate argument (`lowSlopeMatchCert`,
`highSlopeMatchedCert`, `highDataCert`) — follow from the closed form of the
reference core (`CoreClosedForm.lean`) and explicit rational `exp`/`log`
enclosures (`PhaseEnclosure.lean`, `PhaseEnclosureHigh.lean`), with
statements matching the manuscript's displays exactly.  See
`Erdos320/Lemmas/CertLowQ4Positive.lean`, `CertLowSlopeMargin.lean`,
`CertLowCurvature.lean`, `CertLowSlopeMatch.lean`, `CertHighSlopeMatched.lean`,
`CertHighData.lean`.  The `directed_interval_certificate.py` program is a
reproducibility artifact, not a trust dependency; the external axioms are
exactly the four listed in the header: `lowFiniteInput`,
`fioriKadiriSwidinsky_pi_approx`, `dusart_theta_k3`, `bgmsSTable` (matching
the trust boundary the manuscript's reproducibility section reports). -/

end Erdos320
