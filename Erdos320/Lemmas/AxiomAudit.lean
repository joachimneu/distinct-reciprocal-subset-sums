import Lean

/-!
# `#assert_axioms` — build-enforced audit of a theorem's axiom dependencies

`#print axioms thm` *displays* the axioms `thm` transitively depends on; this
file provides the command

```
#assert_axioms thm : [ax₁, …, axₙ]                  -- exactly these, nothing else
#assert_axioms thm : [ax₁, …, axₙ] + native_decide  -- these, plus `native_decide` entries
```

which *checks* the set at compile time. Elaboration **fails** if `thm` depends
on an axiom not listed (a leaked `sorry` would surface as `sorryAx`, a stray
assumption by its name), or if a listed axiom is *not* in the dependency cone
(a stale audit line overstating the trust surface). With the `+ native_decide`
suffix, the per-invocation compiler-trust axioms that `native_decide` records
(names of the form `<decl>._native.native_decide.ax_*`) are additionally
allowed — the accepted trust extension of the `highFiniteInput` cluster (see
`Erdos320/Assumptions.lean`); without the suffix they too are rejected, so the
suffix doubles as a per-theorem statement of *whether* compiled evaluation is
in the cone.

`Erdos320/Main.lean` invokes this once per capstone theorem, so the trusted
core *states* each theorem's complete trust boundary and every build
*re-verifies* it.
-/

namespace Erdos320.AxiomAudit

open Lean Elab Command

/-- Recognizes the per-invocation compiler-trust axioms minted by
`native_decide`: names of the form `<decl>._native.native_decide.ax_*`. -/
def isNativeDecideAxiom : Name → Bool
  | .str (.str (.str _ "_native") "native_decide") s => s.startsWith "ax_"
  | _ => false

/-- Shared elaborator of the two `#assert_axioms` forms: check that the axioms
`thm` depends on are exactly the ones listed in `axs` — plus, when
`allowNative` is set, any `native_decide` compiler-trust entries. -/
def checkAssertedAxioms (thm : Ident) (axs : Syntax.TSepArray `ident ",")
    (allowNative : Bool) : CommandElabM Unit := do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  let expected ← axs.getElems.mapM fun a =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let actual ← liftCoreM <| collectAxioms thmName
  let unexpected := actual.filter fun ax =>
    !expected.contains ax && !(allowNative && isNativeDecideAxiom ax)
  let missing := expected.filter fun ax => !actual.contains ax
  unless unexpected.isEmpty && missing.isEmpty do
    throwErrorAt thm "axiom audit for '{thmName}' failed:{
      ""}\n  depended on but not asserted: {unexpected.toList}{
      ""}\n  asserted but not depended on: {missing.toList}"

/-- See the module docstring: asserts that the axioms `thm` depends on are
exactly the listed ones. -/
elab "#assert_axioms " thm:ident " : " "[" axs:ident,* "]" : command =>
  checkAssertedAxioms thm axs false

/-- See the module docstring: as `#assert_axioms`, but additionally allowing
the per-invocation compiler-trust entries recorded by `native_decide`. -/
elab "#assert_axioms " thm:ident " : " "[" axs:ident,* "]"
    " +" "native_decide" : command =>
  checkAssertedAxioms thm axs true

end Erdos320.AxiomAudit
