# Erdos320

A **Lean 4 + Mathlib** effort to **machine-check a manuscript on Erdős Problem
#320** — *the asymptotic number of distinct reciprocal subset sums* — and, in
doing so, to find out whether the paper's arguments are correct or need
adjustment.

This is a proof **audit**, not an application. The deliverable is checked Lean
— the manuscript's **Theorem 1.1 is fully machine-checked**
(`Erdos320/Main.lean`, `#print axioms`-auditable against exactly four
documented axioms) — together with an honest record of which of the paper's
steps went through unchanged, which needed repair,
and where a stated constant, bound, or lemma turned out to be wrong or vacuous.
**Lean's kernel is the authority**; "the paper says so" is a hypothesis to be
discharged, never a citation that settles anything.

## The problem

For a positive integer `N`,

```text
𝓔_N = { ∑_{n ∈ A} 1/n : A ⊆ {1, …, N} },   S(N) = |𝓔_N|.
```

`𝓔_N` is the set of distinct-denominator Egyptian fractions with denominators
at most `N` (the empty subset contributes `0`, so `S(0) = 1`). There are `2^N`
formal subset sums, but many collide — already `1/2 = 1/3 + 1/6` — so `S(N)`
measures the arithmetic redundancy among bounded-denominator Egyptian
fractions. This is the *image-size* question recorded as
[Erdős Problem #320](https://www.erdosproblems.com/320); it is **distinct** from
the fixed-target problem "how many subsets sum to a prescribed `x`" (see
`CLAUDE.md` for why the two must not be conflated).

## What the manuscript claims

A full asymptotic for `log S(N)` with a **nonconstant** iterated-logarithmic
phase. With `log_j` the `j`-fold iterated logarithm,
`h(N) = max{ j ≥ 3 : log_k N ≥ 1 for every 3 ≤ k ≤ j }` (the first-crossing
stopping depth), and terminal phase `u_N = log_{h(N)} N ∈ [1, e)`,

```text
log S(N) = (N / log N) · (∏_{j=3}^{h(N)} log_j N) · Φ(u_N) · (1 + 1/log₃N + O(1/(log₃N·log₄N))),
```

uniformly in `u_N`, where `Φ : [1,e] → (0,∞)` is positive, continuous, satisfies
`Φ(1) = Φ(e)`, and is **not constant**. The nonconstancy — the heart of the
result — is forced by two finite inputs (certified enclosures of the
normalized count `F` at `N₀ = ⌊e¹⁸⌋` and `N₁ = ⌊e⁶⁵⌋`) that yield
incompatible values (`C < 1.16` and `C > 1.17`) for any hypothetical constant
phase; the directed-interval evaluations that carry those inputs to the
contradiction are **proved inside Lean**.

The proof has three analytic ingredients — an exact large-prime decomposition, a
concave weighted averaging relation, and iteration of that relation along
exponential scales — plus the finite certificates. `CLAUDE.md` breaks this down
into a formalization roadmap.

## Two code pieces

The repository is organized into two self-contained parts, each with its own
README that connects its files to the statements in the manuscript:

1. **[`Erdos320/`](Erdos320/) — the Lean 4 + Mathlib formalization (the proof).**
   The machine-checked development of Theorem 1.1: the definitions, the analytic
   lemmas, the capstone theorems, and the trust boundary. Start at
   [`Erdos320/Main.lean`](Erdos320/Main.lean), the trusted core that restates
   Theorem 1.1 with every object pinned to its definition and all proofs
   delegated to `Erdos320/Lemmas/`. The full paper ↔ Lean map and the
   architecture live in **[`Erdos320/README.md`](Erdos320/README.md)**.

2. **[`ComputationalCertificates/`](ComputationalCertificates/) — the finite
   computations backing the axioms.** The artifacts that justify the
   formalization's finite-input axioms: the C++ enumeration and transcript
   behind the low finite input (`lowFiniteInput`) and the published BGMS
   `S(0..83)` table (`bgmsSTable`), with their provenance and integrity hashes.
   See **[`ComputationalCertificates/README.md`](ComputationalCertificates/README.md)**.

Together they ship the whole trust surface of the mechanization: `Erdos320/`
proves everything downstream of a small, explicit set of axioms, and
`ComputationalCertificates/` holds the finite computations those axioms stand on.

Supporting the two: `Erdos320.lean` (the library umbrella that imports the
modules under `Erdos320/`) and `.claude/` (project instructions and house
rules).
- `.claude/` — project instructions (`CLAUDE.md`) and house rules.

## Build

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.32.0`) and
managed by elan; Mathlib is pinned at `v4.32.0` in `lakefile.toml`.

```bash
lake exe cache get                 # fetch prebuilt Mathlib oleans (do this first)
lake build                         # build the whole project
lake env lean Erdos320/Main.lean   # type-check the trusted core, re-emitting its warnings
```

Do **not** build Mathlib from source; `lake exe cache get` pulls the prebuilt
oleans. A change is "ready" only when `lake build` passes and there are no proof
holes outside the sanctioned axiom file:

```bash
rg -n -w 'sorry|admit|unsafe' Erdos320 | rg -vF '`'             # must be empty (drops doc-comment mentions)
rg -n '^\s*axiom\b' Erdos320 --glob '!Erdos320/Assumptions.lean'  # axiom declarations only in Assumptions.lean
```

`axiom` is permitted only in `Erdos320/Assumptions.lean` (the explicit trust
boundary); a theorem's real dependencies can be audited with `#print axioms`.
See `CLAUDE.md` for the full checks, the auditing stance, and the proof roadmap.
