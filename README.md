# QuditCliffordLean

Lean 4 formalization of **A Complete and Natural Rule Set for Multi-Qudit Clifford Circuits in All Odd Prime Dimensions**, by Bian, Li, Ross, van de Wetering, and Zhao.

**Status: partial. The paper's main completeness theorem (Theorem 4.10) is not yet proved.** The project contains checked matrix, Pauli, symplectic, circuit, and rewrite results. Unfinished results are recorded as proof obligations, not filled with `sorry` or assumed as axioms.

The selected convention is **Figure 1: exact matrix equality with scalar generator `-ω`**, and raw multipliers `M_a|j⟩=|aj⟩`. Projective equality and symplectic equality remain distinct from exact equality.

## Build and check

The project pins **Lean 4.19.0** and **mathlib v4.19.0**, with dependency commits in `lake-manifest.json`.

```sh
lake exe cache get
./scripts/check.sh
```

The check script builds the library and checks the transitive logical dependencies of the formal declarations. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms are allowed; admitted proofs and project-specific axioms are rejected. The GitHub workflow runs the build and audit as well.

On this local checkout, an ignored toolchain and dependency cache are included under `.lake/`; `scripts/check.sh` finds the cached toolchain if `lake` is not on PATH. A fresh clone should install [Lean via elan](https://lean-lang.org/install/manual/) first; the pinned `lean-toolchain` selects the version. CI uses the official [lean-action](https://github.com/leanprover/lean-action). CI configuration has been added, but no remote CI run or push is claimed.

## What is proved

- The actual complex roots `ω` and `-ω`, including the latter's exact order `2d` in odd dimension.
- Exact matrices for X, Z, H, S, CZ and raw multipliers; unitarity, finite orders, Pauli commutation and generator conjugation. H uses the paper's phase normalization.
- A faithful multi-qudit Pauli matrix representation, including the sign extension required by Figure 1; exact normal-form uniqueness and cardinality.
- The Pauli centralizer theorem: every complex matrix commuting with all Pauli X and Z operators is scalar. Equal conjugation actions of unitaries therefore imply equality up to phase.
- The nondegenerate alternating phase-space form, the induced action of scalar-fixing Pauli automorphisms, its inner-Pauli kernel, and an explicit splitting in odd dimension.
- The actual unitary matrix normalizer, its symplectic-action homomorphism, and its kernel: matrices projectively equal to Paulis. This full normalizer includes arbitrary unitary scalars; its identification with the generated circuit group remains open.
- Concrete Figure 6 A/B/D/E boxes, arbitrary-wire Z/X normalizations, and the literal recursive symplectic normal form with existence and uniqueness (Lemmas 3.4–3.7 and Proposition 3.8). Its syntax count proves the cardinality formula for the existing symplectic group (Lemma 3.9). These are exponent-level results.
- **Exact soundness of all sixteen fully expanded Figure 1 rules and their rewrite closure**, on arbitrary named wires in every odd prime dimension. This is `Circuit.figure1_sound`; completeness is separate.
- The exact derived X, Z, CX, SWAP, remote-CZ, and multiplier words on arbitrary named wires, including every scalar. The signed quadratic Gauss-sum evaluation and `det(H)=1` are proved using Vandermonde factorization, finite phase sums, and unitarity. The phase-gate and controlled-Z determinants are checked too.
- Concrete primitive circuits, all sixteen syntactic rewrite schemas, contextual rewriting, and arbitrary-register unitary denotation.
- A complete exact rewrite presentation for the ordinary Pauli subgroup, with Weyl phases retained. This is a separate block presentation, not the sixteen-rule Clifford presentation.
- C0 normalization and completeness for scalar words; exact Figure 1 soundness and completeness in arity zero.

The precise theorem-to-paper mapping and remaining hypotheses are in **[docs/STATUS.md](docs/STATUS.md)**. The source convention audit and full obligation inventory are in **[docs/PAPER_AUDIT.md](docs/PAPER_AUDIT.md)**.

## What remains

The main missing work is the generated Clifford-group correspondence and scalar characterization; the primitive-circuit interpretation of the symplectic normal form; the 42 box relations and their derivation from the 18 symplectic relations; and the explicit projective-to-exact lifting for the sixteen rules. Concrete pair normalization and named-wire rule transport are now checked; these do not establish rewriting completeness.

`QuditClifford.Circuit.MainTheorem` is the precise **target proposition**, not a theorem asserted by this development. It is not assumed by the checked proofs. A successful build does not assert this proposition.

## Layout and conventions

`QuditClifford.lean` imports the complete checked library. `Audit.lean` validates its logical dependencies. The source modules are under `QuditClifford/`; definitions and theorem comments identify their mathematical scope.

- Matrices have output rows and input columns.
- Products and circuit lists use matrix order: the rightmost factor acts first.
- Pauli coordinates `(c,x,z)` represent `ω^c X^x Z^z`; phase space uses `(z,x)`, as in Definition 2.25.
- The enlarged exact Pauli model is an independent sign times the ordinary Pauli group; oddness is required for the enlarged matrix representation to be injective.
- Fractions in gate exponents are inverses in `ZMod d`, followed by ordinary natural powers; they are not complex fractional powers.
- General lemmas sometimes hold for every nonzero or odd dimension. Their Lean hypotheses state that broader valid scope; this does not extend the paper's Clifford completeness theorem to composite dimensions.
- The circuit model uses named wires and explicit distinctness proofs for controlled-Z gates. Its wiring coherence and correspondence to the paper's diagrams are documented in the source audit.

## Source snapshot

The supplied PDF was read without changing it or its TeX sources:

- Title as above; 78 pages; PDF creation timestamp 19 September 2026.
- Local source: `/Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qudit-quantum.pdf`.
- SHA-256: `87a80645240abf74545fa6266ed5565cabb790faae674a2ba49d7c338873a542`.

The PDF mixes the selected Figure 1 scalar convention with older omega-only prose. This project follows the user's explicit choice of Figure 1 and records the affected source claims instead of silently treating inconsistent statements as theorems.
