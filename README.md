# Erdos320

A **Lean 4 + Mathlib** effort to **machine-check a manuscript on Erdős Problem #320** — *the asymptotic number of distinct reciprocal subset sums*. The deliverable is checked Lean — the manuscript's **Theorem 1.1 is fully machine-checked** (`Erdos320/Main.lean`, with `#print axioms` auditable against exactly four axioms, documented in `Erdos320/Assumptions.lean`, capturing the proof's external inputs — results re-used from the literature together with finite computational certificates).

**Use of AI:** The computational certificates in `ComputationalCertificates` were produced by GPT 5.6 Sol. The Lean proof in `Erdos320` was produced by Fable 5, based on a paper draft produced with the assistance of GPT 5.6 Sol. We have carefully verified/curated the computational certificates, as well as the trusted core of the Lean proof (`Erdos320/Main.lean`, `Erdos320/Assumptions.lean` — no `sorry`, `axiom`, etc., elsewhere in the code base).

## The problem

For a positive integer `N`, let

```text
𝓔_N = { ∑_{n ∈ A} 1/n : A ⊆ {1, …, N} },   S(N) = |𝓔_N|.
```

`𝓔_N` is the set of distinct-denominator Egyptian fractions with denominators
at most `N` (the empty subset contributes `0`, so `S(0) = 1`). There are `2^N`
formal subset sums, but many collide — already `1/2 = 1/3 + 1/6` — so `S(N)`
measures the arithmetic redundancy among bounded-denominator Egyptian
fractions. This is the *image-size* question recorded as
[Erdős Problem #320](https://www.erdosproblems.com/320) (it is distinct from
the fixed-target problem "how many subsets sum to a prescribed `x`").

## What the manuscript claims

**A full asymptotic for `log S(N)` with a nonconstant iterated-logarithmic
phase.** With `log_j` the `j`-fold iterated logarithm,
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
phase.

The proof has three analytic ingredients — an exact large-prime decomposition, a
concave weighted averaging relation, and iteration of that relation along
exponential scales — plus the finite certificates.

## Two code pieces

The repository is organized into two self-contained parts, each with its own
README that connects its files to the statements in the manuscript:

1. **[`Erdos320/`](Erdos320/) — the Lean 4 + Mathlib formalization (the proof).**
   The machine-checked development of Theorem 1.1. Start at
   [`Erdos320/Main.lean`](Erdos320/Main.lean), the trusted core that restates
   Theorem 1.1 with every object pinned to its definition and all proofs
   delegated to `Erdos320/Lemmas/`. The full paper ↔ Lean map and the proof
   architecture live in **[`Erdos320/README.md`](Erdos320/README.md)**.

2. **[`ComputationalCertificates/`](ComputationalCertificates/) — the finite
   computations backing the axioms.** The artifacts that justify the
   formalization's finite-input axioms.
   See **[`ComputationalCertificates/README.md`](ComputationalCertificates/README.md)**.

Thus, `Erdos320/` proves everything downstream of a small, explicit set of axioms, and
`ComputationalCertificates/` holds any finite computations those axioms stand on.

## Build

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.32.0`) and
managed by elan; Mathlib is pinned at `v4.32.0` in `lakefile.toml`.

```bash
lake exe cache get                 # fetch prebuilt Mathlib oleans (do this first)
lake build                         # build the whole project
lake env lean Erdos320/Main.lean   # type-check the trusted core, re-emitting its warnings
```

To verify that there are no proof holes outside the sanctioned assumptions file:

```bash
rg -n -w 'sorry|admit|unsafe' Erdos320 | rg -vF '`'             # must be empty (drops doc-comment mentions)
rg -n '^\s*axiom\b' Erdos320 --glob '!Erdos320/Assumptions.lean'  # axiom declarations only in Assumptions.lean
```
