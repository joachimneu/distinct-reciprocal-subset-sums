# Trusted core & the axiom boundary

Two invariants of the `Erdos320` formalization. Both are load-bearing for the
audit's credibility; treat them as hard constraints.

## 1. Axioms/assumptions live **only** in `Erdos320/Assumptions.lean`

`Erdos320/Assumptions.lean` is the single, explicit trust boundary — the only
place where an unproved fact may be assumed. It holds exactly the manuscript's
external inputs (results cited from the literature) and its computer-assisted
finite certificates, each documented with (a) where the paper uses it and
(b) where it comes from.

**Nowhere else** may a `sorry`, `admit`, `unsafe`, or a hand-declared `axiom`
appear. A resisting step of the paper's own argument becomes a named `def` or an
explicit hypothesis parameter — never an axiom outside this file, and never a
proof hole. Verify:

```bash
rg -n -w 'sorry|admit|unsafe' Erdos320 | rg -vF '`'              # must be empty
rg -n '^\s*axiom\b' Erdos320 --glob '!Erdos320/Assumptions.lean' # must be empty (declarations; prose mentions in doc-comments don't match)
```

and audit any theorem's real dependencies with `#print axioms <thm>`: it must
list only the `Assumptions.lean` axioms plus Lean's `propext`,
`Classical.choice`, `Quot.sound` — plus, solely via the `highFiniteInput`
cluster (nonconstancy side), the accepted `native_decide` compiler-trust
entries. Anything else is a leaked hole and a defect. See the full
trust-boundary policy in `CLAUDE.md`.

## 2. `Erdos320/Main.lean` is the trusted core — do not touch it unless explicitly instructed

`Erdos320/Main.lean` restates the paper's **Theorem 1.1** with every object in
the statement pinned to its definition (`rfl`-checked) and all proofs delegated
to `Erdos320/Lemmas/`. It is the one file a reader inspects to confirm *what* is
proved and *that it is the right theorem* — its entire value is being a stable,
carefully scrutinized front page.

Therefore **do not edit `Main.lean` unless the user explicitly asks you to.** In
particular: do not add proofs to it, do not "tidy" or restructure it, and do not
rewrite its restated statements to accommodate a refactor. If a lemma it invokes
changes shape so that the delegation no longer type-checks, that is a signal to
raise with the user — not license to edit the core. New results and all proof
work go in `Erdos320/Lemmas/`; `Main.lean` only ever *invokes* them.
