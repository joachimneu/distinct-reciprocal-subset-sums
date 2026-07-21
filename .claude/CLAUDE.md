# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

`Erdos320` — a **Lean 4 + Mathlib** formalization effort whose goal is to
**machine-check a specific manuscript** on **Erdős Problem #320** (the
asymptotic number of distinct reciprocal subset sums), *in order to find out
whether its arguments are correct or need adjustment*. This is proof-audit
research, not an application: we are re-deriving the paper's claims inside
Lean's kernel and reporting exactly which steps go through, which need repair,
and where a stated bound or lemma turns out to be false or vacuous.

The object of study is
```text
𝓔_N = { ∑_{n ∈ A} 1/n : A ⊆ {1, …, N} },   S(N) = |𝓔_N|,
```
and the paper's **main theorem** is a full asymptotic for
`log S(N)` with an explicit error term:
```text
log S(N) = (N / log N) · (∏_{j=3}^{h(N)} log_j N) · Φ(u_N) · (1 + 1/log₃N + O(1/(log₃N·log₄N))),
```
uniformly in the terminal phase `u_N = log_{h(N)} N ∈ [1, e)`, where
`Φ : [1,e] → (0,∞)` is positive, continuous, `Φ(1) = Φ(e)`, and — the crux —
**nonconstant**. Nonconstancy is what makes the leading factor genuinely
oscillate rather than tend to a limit, and it is established by two finite,
reproducible certificate inputs (the `F`-enclosures at `⌊e¹⁸⌋` and `⌊e⁶⁵⌋`)
whose directed-interval consequences are proved inside Lean.

**Lean is the authority.** Propose statements, constructions, and proof steps
freely, but never assert a mathematical fact (an identity, a bound, a lemma of
the paper) as *verified* until Lean has checked it. Keep believed-but-unchecked
claims — including claims that the paper's own steps are correct — marked as
provisional. "The paper says so" is a hypothesis to
be discharged, not a citation that settles anything.

## Auditing stance: the paper is under test, not assumed correct

The whole point is to check the manuscript, so treat every step as suspect
until Lean confirms it:

- When a paper step resists formalization, that is *data*, not just a Lean
  inconvenience — it may indicate a gap, an unstated hypothesis, an off-by-one
  in a constant, or a genuine error. Record it before
  routing around it. Do **not** paper over a gap with a stronger hypothesis and
  then quietly forget you did.
- A resisting step of *the paper's own argument* becomes a named `def` or an
  explicit hypothesis parameter of the theorem, so the dependence is visible in
  the statement — never a `sorry`, `admit`, or `unsafe`, and never a
  hand-declared `axiom` (axiomatizing the paper's own reasoning would defeat the
  audit). See Hard constraints and the trust-boundary policy below.
- If the Lean development forces a *change* to a constant, an inequality
  direction, a stopping rule, or a lemma statement relative to the paper, that
  is a finding: state it plainly, cite the Lean file, and log it. The
  deliverable includes "here is what had to change."
- Beware vacuous success: a mis-stated definition (e.g. dropping a range
  restriction, mis-encoding the empty-sum convention `S(0)=1`, or weakening a
  uniformity to a pointwise claim) can make a theorem compile while proving
  nothing. Before trusting a green build, confirm the statement still says what
  the paper claims.

## Trust boundary: axioms live only in `Erdos320/Assumptions.lean`

The formalization is allowed exactly one hole in its wall, and it is explicit.
Everything the manuscript imports from **outside** its own reasoning — results
cited from the literature (e.g. explicit prime-number / Chebyshev estimates)
and the **computer-assisted lemmas** whose proof is a finite computation done by
an external certificate program — is declared as an `axiom` in
`Erdos320/Assumptions.lean`, and **nowhere else**. Each such axiom must document,
in its doc-comment, **(a) where it is used in the paper** (the `\label{…}` name)
and **(b) where it comes from** (a literature citation, or the specific
certificate program whose repo-tracked copy lives in
`ComputationalCertificates/`). The boundary
currently holds **exactly four axioms** (`lowFiniteInput`,
`fioriKadiriSwidinsky_pi_approx`, `dusart_theta_k3`, `bgmsSTable`); the
directed-interval certificate evaluations are proved theorems
(`Erdos320/Lemmas/Cert*.lean`) — do not re-axiomatize them. The **high finite
input** `F(⌊e⁶⁵⌋) > 3.2411` (`comp:high`) is likewise **not an axiom**: it is the
proved theorem `highFiniteInput` in `Erdos320/Lemmas/HighFiniteAssembly.lean`
(154 tight per-shell collision contributions + one aggregate block over
`155 ≤ m ≤ 10⁶`), resting only on `bgmsSTable` (the published BGMS `S(0..83)`
table) + `dusart_theta_k3` (Dusart 2018 Thm 4.2's k = 3 row — the consumed
`0.006788·t/log t` form, `dusart_theta_approx`, is a theorem derived from it
in `Lemmas/ShellCountDusart.lean`) + Lean. Only the
**low** finite input remains a
program-transcript axiom (its ~10¹³-operation enumeration is not feasibly
reproducible in Lean). Do not re-axiomatize `highFiniteInput`.

Everything downstream of those axioms must be genuinely proved: no `sorry`,
`admit`, `unsafe`, or hand-declared `axiom` may appear in any other file. The
payoff is that the entire trust boundary of a theorem is auditable with
`#print axioms <thm>`: it must show only the axioms in `Assumptions.lean`,
Lean's own foundational three (`propext`, `Classical.choice`, `Quot.sound`),
and — solely via the `highFiniteInput` cluster
(`Doublings`/`HighShellGrid*`/`HighAggregate`) — the **accepted
`native_decide` compiler-trust family** (entries of the form
`….ax_*` under `_native.native_decide`, one per invocation; the
uniformity-side capstones `erdos320_theorem_1_1_uniform_error` /
`_uniformity` carry none and remain kernel-only on FKS alone).  Anything
else in that list is a leaked hole and a defect.

When an external input cannot yet be *stated* (its objects — Chebyshev `ϑ`, the
phase `Φ`, the backward-reference functions — are not defined yet), record it in
the "Not yet formalizable" section of `Assumptions.lean` as prose, and add the
real axiom there once the objects exist. Do not approximate it with a
placeholder axiom over the wrong objects.

## Terminology: two related but distinct counting problems (do not conflate)

The paper's introduction is explicit that #320 is **not** the fixed-target
Egyptian-fraction problem; keep them apart:

1. **Image-size problem** (this project's subject, Erdős #320): count the size
   `S(N) = |𝓔_N|` of the *image* of the subset-sum map `A ↦ ∑_{n∈A} 1/n` over
   `A ⊆ {1,…,N}`. The target rational is allowed to vary; collisions
   (e.g. `1/2 = 1/3 + 1/6`) are what make `S(N) < 2^N`.
2. **Fixed-target problem** (related but different): fix a rational `x` and
   count the *subsets* `A ⊆ {1,…,N}` with `∑_{n∈A} 1/n = x` — one fibre of the
   same map. The case `x = 1` was resolved by Conlon–Fox–He–Mubayi–Pham–Suk–
   Verstraëte and by Liu–Sawhney; this is **not** what #320 asks.

Never state a result "about #320" that is secretly about a single fibre.

## Build & required checks

Toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.32.0`), managed by
elan; the devcontainer installs it. `lakefile.toml` declares one lean_lib
(`Erdos320`) and requires **Mathlib** pinned at `v4.32.0`.

```bash
lake exe cache get                       # fetch prebuilt Mathlib oleans — do this before the first build
lake build                               # build the default target (the whole project)
lake env lean Erdos320/Defs/Basic.lean   # type-check a single file fast (forces recompile, re-emits its warnings)
```

Do **not** build Mathlib from source — `lake exe cache get` pulls the prebuilt
oleans (thousands of files); a cold `lake build` without it will try to compile
Mathlib and take a very long time.

A change is not "ready" until `lake build` passes and no proof holes were
introduced *outside the sanctioned axiom file*:

```bash
rg -n -w 'sorry|admit|unsafe' Erdos320 | rg -vF '`'                # must be empty (the `| rg -vF '`'` drops doc-comment mentions of these words)
rg -n '^\s*axiom\b' Erdos320 --glob '!Erdos320/Assumptions.lean'   # must find nothing (axiom *declarations* only in Assumptions.lean; prose mentions of the word in doc-comments don't match the anchored form)
```

(The build itself also warns "declaration uses 'sorry'" on any real `sorry`/
`admit`, so a clean `lake build` with no such warning is the first line of
defense; the grep catches `unsafe` and any that slip through.)

`axiom` is permitted **only** in `Erdos320/Assumptions.lean` (see the trust-
boundary policy above). To confirm a theorem depends on nothing beyond the
declared axioms, run `#print axioms <thm>` — it must list only the
`Assumptions.lean` axioms plus `propext`, `Classical.choice`, `Quot.sound`
(plus, on the nonconstancy side only, the accepted `native_decide`
compiler-trust entries from the `highFiniteInput` cluster).

The `/my-lean-check-nonfishy` skill does a deeper trustworthiness audit (catches
`sorry`, hand-declared axioms, kernel-weakening options, unreachable decoy files,
trivial statements). It will flag the `Assumptions.lean` axioms — that is
expected; they are the intended, documented trust boundary. `native_decide` is
accepted.

**Resolve every compiler/linter warning, even when the build is green** (unused
variables/hypotheses, unused `simp` args, deprecations). Lean caches `.olean`s,
so a plain `lake build` on an up-to-date tree re-emits nothing — recheck a
touched file with `lake env lean <file>` (which forces recompilation) to see its
warnings before calling the change done.

## Architecture (the big picture)

The Lean namespace tracks the folder: everything is under `namespace Erdos320`.
The manuscript's Theorem 1.1 is fully formalized; the development is large,
including the certificate-proof cluster
`CoreClosedForm`/`PhaseEnclosure(High)`/`Cert*` that proves the
directed-interval evaluations, and the `highFiniteInput` assembly
`HighFiniteAssembly`/`HighShellGrid1-8`/`HighAggregate` that proves the
high finite input.

- **`Erdos320/Main.lean`** — **the trusted core; read this first.** It restates
  the paper's **Theorem 1.1** (`thm:main`) in full, pins every object in the
  statement (`S(N)`, `log_j`, `h(N)`, `u_N`) to its definition with `rfl`-checked
  recap lemmas, and delegates all proofs to `Erdos320/Lemmas/` — proofs
  deliberately do **not** live here. This is the one file to read to check *what*
  is proved and *whether it is the right theorem*. Auditable with
  `#print axioms Erdos320.erdos320_theorem_1_1`.
  **`Main.lean` and `Assumptions.lean` are the two "read-me-to-trust-everything"
  files** — a human gains confidence in the whole mechanization by inspecting
  *only* these two (Main = the exact claim; Assumptions = everything assumed).
  So keep both **deliberately minimal**: `Main.lean` holds only statement
  restatements + one-line invocations of `Lemmas/`; put **no** proofs, helper
  lemmas, `have`-chains, computation, or new definitions here. New work goes in
  `Lemmas/`. (Do not edit `Main.lean` at all unless the user explicitly asks —
  see Hard constraints.)
- **`Erdos320/README.md`** — the Lean sub-area's front page: an overview of the
  formalization plus the paper ↔ Lean map (every numbered paper item and each
  key defined object mapped to its Lean location). Keep it current when adding or
  renaming paper-facing declarations.
- **`Erdos320.lean`** (repo root) — the umbrella/library entry point; just
  `import`s the modules under `Erdos320/` (including `Erdos320.Main`).
- **`Erdos320/Defs/`** — the load-bearing definitions on top of Mathlib. The
  base module is `Defs/Basic.lean`
  (`reciprocalSubsetSumSet (N : ℕ) : Finset ℚ` = `𝓔_N`; `S (N : ℕ) : ℕ` =
  `|𝓔_N|`; `F (N : ℕ) : ℝ` = `(log N / N)·log S(N)`) plus honestly proven basics
  (`S 0 = 1`, `1 ≤ S N`, `Monotone S`); the rest of `Defs/` adds `iteratedLog`,
  `stoppingDepth`/`phaseCoordinate`, the averaging profile `𝓑` and `H̄_r`/`ρ_r`,
  modular images `σ`, ….
- **`Erdos320/Lemmas/`** — the proof: the analytic development plus the capstone
  theorems in `Lemmas/Main.lean` (`main_asymptotic`, `main_uniformity_tendsto`)
  and `Lemmas/MainTheorem.lean` (`erdos320_main`, `erdos320_main_exists`) that
  `Main.lean` invokes.
- **`Erdos320/Assumptions.lean`** — the **only** file permitted to declare
  `axiom`s: the trust boundary (external literature inputs + computer-assisted
  finite certificates), each documented with its paper location and source. See
  the trust-boundary policy above and `Erdos320/README.md` for the current axiom
  list.
  Like `Main.lean`, this is a **read-me-to-trust-everything** file, so keep it
  **axioms-only and minimal**: put here *only* the `axiom` declarations (plus the
  bare definitions an axiom's own statement needs, e.g. `bgmsTable`) and their
  documentation. **Do not** put derived theorems, helper lemmas, or `have`-proofs
  here, even when they are proved *from* these axioms — a theorem derived from an
  axiom belongs in `Lemmas/` (e.g. `dusart_theta_approx`, the consumed
  `0.006788·t/log t` form, is proved in `Lemmas/ShellCountDusart.lean` from the
  axiom `dusart_theta_k3`, not in this file). The point is that a human auditing
  the trust surface reads a short list of clearly-labelled assumptions and
  nothing else.

`reciprocalSubsetSumSet`, `S`, and `F` are the **load-bearing definitions**: the
meaning of any theorem targeting the paper lives entirely in them. Mis-stating
them (dropping the `{1,…,N}` range, the empty-sum contribution, or the `ℚ`-valued
exactness) can make a downstream result **vacuous while still compiling**. Prefer
building new statements *on top of* Mathlib primitives (`Finset`, `Finset.Icc`,
`ℚ`, `Real.log`) rather than re-deriving them.

### The paper's proof, as a formalization roadmap

The manuscript factors into pieces that can be formalized somewhat
independently (paper labels in parentheses):

1. **Exact large-prime decomposition** (`prop:large-prime-decomposition`,
   `lem:average-collision`) — reduce `S(N)` to a product of modular-image
   sizes `|B_{p,m}|` over prime shells `⌊N/p⌋ = m`.
2. **Concave averaging relation** (`prop:averaging-relation`, `lem:B-slopes`,
   `lem:threshold`) — express the normalized count at one scale as a concave
   weighted average at smaller scales, with explicit error.
3. **Iteration along exponential scales** (`lem:iteration-endpoint-matching`,
   `prop:phase`) — iterate the averaging relation, match endpoints of
   successive scales, and extract the phase `Φ` and the `1/log₃N` second term.
4. **Backward reference functions** (`sec:backward-reference`) — the profile a
   *hypothetical constant* phase would be forced to have; formal Laurent-
   polynomial algebra.
5. **Nonconstancy via breakpoint chords** (`lem:breakpoint-chords`,
   `sec:certificates`) — two finite interval certificates yield the
   incompatible `C < 1.16` and `C > 1.17` for that hypothetical constant, so
   `Φ` cannot be constant. Backed by the finite certificate computations
   (including the C++ low-input enumeration `pilot_mod_images.cpp` under
   `ComputationalCertificates/`).

The finite certificates (integer / exact-rational-interval computations) are the
most tractable Lean targets and a natural early milestone; the analytic
uniformity arguments (steps 2–3) are the hardest.

## Working with the user

- The user often dictates via speech-to-text, so text may contain
  mistranscriptions — words that are wrong but *sound* like what was meant. When
  a request reads oddly, prefer the phonologically nearest plausible reading, act
  on it, and note how you resolved the ambiguity. (E.g. "Erdős 320" may arrive as
  "air dish", "urdos", etc.)
- Replies should be concise and bottom-line-first: lead with the answer plus
  anything surprising; skip restating the question and narrating routine steps.
- **Git is the user's job.** The user commits and rearranges the tree
  concurrently in the background; expect it to change under you. Do not stage,
  commit, pull, push, branch, stash, reset, or tag unless explicitly asked — make
  file edits and stop. Full policy: `.claude/rules/git-operations.md`.
- Do not add test scaffolding, CI, or other unrequested tooling. Here, "the
  tests" are `lake build` plus the no-holes checks above.

## Hard constraints

- Do not introduce `sorry`, `admit`, or `unsafe` anywhere, and do not leave
  proof holes. **Axioms/assumptions are tolerated in exactly one file,
  `Erdos320/Assumptions.lean`, and nowhere else** — only for genuine
  external/computer-assisted inputs, and only with the documented
  (used-in-paper / taken-from) doc-comment. Everywhere else a resisting step
  becomes a named `def` or a hypothesis parameter (see the trust-boundary
  policy and auditing stance above, and `.claude/rules/trusted-core-and-axioms.md`).
- **Do not touch `Erdos320/Main.lean` unless the user explicitly instructs you
  to.** It is the trusted core — the front page that restates Theorem 1.1 with
  proofs delegated to `Erdos320/Lemmas/`. Do not add proofs to it, tidy it, or
  rewrite its statements to accommodate a refactor; new results and proof work
  go in `Erdos320/Lemmas/`, which `Main.lean` only invokes. See
  `.claude/rules/trusted-core-and-axioms.md`.
- Do not fork or re-derive Mathlib definitions this project builds on
  (`Finset`, `Finset.Icc`, `ℚ`, `Real.log`, big operators, …); build on them.
- Do not "fix" the paper into triviality: proving a weaker or differently-scoped
  statement than the manuscript's, or silently strengthening a hypothesis to
  make a step go through, defeats the purpose. If the honest statement will not
  close, say so and log it rather than retreating to a vacuous one.
- Do not declare a paper step "verified" (or "refuted") on the strength of an
  informal argument; only Lean's kernel settles that.

## Methodology & house rules (`.claude/rules/`)

Consult these when relevant:

- **Naming (applies to every identifier** — declarations, fields, locals,
  hypotheses, files, folders): name things so a cold reader knows what they are
  without reading the body. Err toward longer and more explicit; mirror the
  paper's names where they are already descriptive (`reciprocalSubsetSumSet`,
  `averagingRelation`, …). Avoid cryptic single-letter names except where they
  match established mathematical notation in the paper (`S`, `F`, `Φ`).
- `trusted-core-and-axioms.md` — the two hard invariants: axioms/assumptions
  live only in `Erdos320/Assumptions.lean`, and `Erdos320/Main.lean` (the
  trusted core) is not edited unless the user explicitly asks.
- `git-operations.md` — never touch the index / commit unless explicitly told.
