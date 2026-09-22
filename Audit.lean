import QuditClifford
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every kernel-safe total project declaration, including private helpers, and all
of its transitive kernel dependencies. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed; `sorryAx`, custom axioms, and the native-decide trust
axiom `Lean.ofReduceBool` are rejected.

Why the safety check matters: Lean also exports unsafe executable compiler
artifacts named `_cstage1`, `_cstage2`, `_spec_*`, and `_elambda_*`. For example,
compilation of the safe quotient multiplication in `PauliRewrite` produces an
unsafe `Quotient.map₂..._spec_1` axiom for erased runtime code. That axiom is NOT
a dependency of the safe definition or of `PauliRewrite.complete`. Auditing
runtime artifacts as independent roots therefore reports unrelated compiler
implementation axioms as if the mathematical proofs used them.

We exclude unsafe and partial declarations only from the set of audit ROOTS, by Lean's
actual safety metadata rather than a name-pattern exception. We do not whitelist
any compiler axiom. The unrestricted transitive dependency traversal of every
safe declaration is followed by a second check rejecting any reached unsafe or
partial declaration. Thus an unsafe artifact cannot be hidden in a checked
mathematical dependency chain. Theorems always belong to the audited roots.
Generated partial `_unsafe_rec` definitions are treated by the same principle:
exclude only as roots, reject if reached from any audited declaration.

Validation: the audit was run on the project; independent `#print axioms` checks
of `PauliRewrite.complete` and `PauliRewrite.derives_iff_matrix_eq` report exactly
the same three standard axioms. Negative tests in temporary files injected a
safe custom axiom, a private custom axiom, a transitively used external custom
axiom, a sorry proof, and a native-decide proof into the QuditClifford namespace; each was rejected. Those test declarations
are not included in the library.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let projectDeclarations := env.constants.toList.filter fun (name, _) =>
    (Lean.privateToUserName name).getRoot == `QuditClifford
  let names := projectDeclarations.filterMap fun (name, ci) =>
    if ci.isUnsafe || ci.isPartial then none else some name
  if names.isEmpty then throwError "No kernel-safe QuditClifford declarations were loaded."
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in state.axioms do
    unless allowed.contains axiomName do
      throwError "Unapproved axiom dependency: {axiomName}"
  for name in state.visited.toList do
    if let some ci := env.checked.get.find? name then
      if ci.isUnsafe || ci.isPartial then
        throwError "Unsafe or partial mathematical dependency: {name}"
  logInfo m!"Checked {names.length} kernel-safe total project declarations and their transitive dependencies; excluded {projectDeclarations.length - names.length} unsafe/partial runtime roots. Axioms: {state.axioms}."
