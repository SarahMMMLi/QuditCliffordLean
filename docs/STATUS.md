# Formalization status

**This is a partial, kernel-checked formalization. The paper's Theorem 4.10 is not yet proved.** Exact soundness is proved for every arity. Its zero-wire completeness specialization is proved; positive-arity rewrite completeness remains unfinished. The exact target is recorded as the proposition `QuditClifford.Circuit.MainTheorem`; no declaration assumes or proves it. The selected scalar convention is Figure 1's `sigma=-omega`, with exact complex-matrix equality.

Every item marked checked below names an existing proved Lean declaration. A relation's raw-matrix soundness, its expanded circuit soundness, and completeness of the generated rewrite system are separate claims. No rewrite system here has a constructor that admits arbitrary semantic equality as a rewrite.

## Checked foundations and source coverage

| Source | Checked declarations | Scope and remaining distinction |
|---|---|---|
| Definition 2.1; Appendix A.1 | `omega_exp`, `omega_primitive`, `phase_injective`, `phase_sum`, `phase_add`, `phase_star` in `RootOfUnity.lean` | Actual standard complex character of `ZMod d`; nonzero dimensions, including composites. |
| Figure 1 C0 and its scalar convention | `scalarGenerator_primitive`, `scalarGenerator_pow_dimension`, `scalarGenerator_pow_dimension_add_one` | Exact order `2*d` for `-omega` in odd dimension; identifies the complex sign and omega. This is not yet a characterization of all phases in the generated Clifford group. |
| Definition 2.8; equations (6)-(7); A.2-A.5 | `X_pow_dimension`, `Z_pow_dimension`, `clock_shift`, `ZX_eq_omega_XZ`, `ZX_ne_XZ` in `Gates.lean` | Exact matrices, with the Weyl phase retained. |
| Definition 2.9; ordered Pauli algebra | `Pauli.normal_form`, `Pauli.normal_form_unique`, `Pauli.commutation`, `Pauli.commute_iff`, `Pauli.same_exponents_iff` | Abstract finite Heisenberg group with explicit cocycle. |
| Matrix realization of the Pauli algebra | `Pauli.reprHom`, `Pauli.repr_injective`, `Pauli.matrix_normal_form_unique`, `Pauli.card_matrix_range` | Faithful actual complex representation; exact coordinate uniqueness and matrix cardinality `d^(2*n+1)`. |
| Selected enlarged Pauli scalar convention | `SignedPauli.reprHom`, `SignedPauli.repr_injective`, `SignedPauli.repr_scalarGenerator`, `SignedPauli.card_matrix_range` | Independent sign times ordinary Pauli; faithful in odd dimension, actual matrix cardinality `2*d^(2*n+1)`. |
| Definition 2.10; Proposition 2.12; A.7,A.13,A.14 | `H_sq`, `H_sq_exact`, `lambda_sq`, `H_pow_four`, `S_pow_dimension`, `CZ_pow_dimension` | The paper's exact Fourier normalization, including the sign in H squared. |
| Unitarity of basic gates | `H_unitary`, `S_unitary`, `CZ_unitary`, `X_unitary`, `Z_unitary`, `multiplier_unitary` | Actual complex adjoints, not an abstract unitary model. |
| Lemma 2.23 | `HXH_adjoint`, `HZH_adjoint`, `SXS_adjoint`, `SZS_adjoint` | Exact single-qudit conjugations; the S-X formula requires odd dimension. |
| Lemma 2.24 | `CZ_X₁`, `CZ_X₂`, `CZ_Z₁`, `CZ_Z₂` | Exact two-qudit pushing identities; equivalent to conjugation after using CZ unitarity. |
| Proposition 2.21 | `pauli_centralizer`, `scalar_of_commutes_paulis`, `scalar_ratio_of_same_pauli_action` in `Centralizer.lean` | Proved directly for full multi-qudit complex matrices; commuting with all X and Z implies scalar. |
| Equality up to phase | `ProjectiveEq`, `projectiveSetoid`, `projectiveEq_of_same_pauli_action`, `unitary_projectiveEq_of_same_pauli_action` in `Projective.lean` | Genuine nonzero-scalar equivalence, kept distinct from exact equality. Does not yet identify the generated Clifford quotient with a symplectic group. |
| Definition 2.25 | `symplecticLinear`, `symplectic_nondegenerate`, `symplecticGroup` in `Symplectic.lean` | Actual nondegenerate alternating form and subgroup of linear equivalences preserving it. |
| Pauli phase-space coordinates | `Pauli.coordsHom`, `Pauli.coords_surjective`, `Pauli.coords_eq_iff`, `Pauli.commutatorPhase_eq_symplectic`, `Pauli.commute_iff_symplectic` | Coordinate quotient and commutator pairing; coordinate order matches the paper's Z-first convention. |
| Scalar-fixing Pauli automorphisms | `Pauli.actionEquiv`, `Pauli.symplecticAction`, `Pauli.trivial_action_iff_inner`, `Pauli.inner_eq_iff_coords_eq` in `PauliAutomorphisms.lean` | The actual induced exponent action preserves the symplectic form; its kernel consists exactly of inner Pauli automorphisms, with unique correcting exponents. |
| Abstract split exact sequence | `Pauli.liftSymplectic`, `Pauli.actionHom`, `Pauli.liftHom`, `Pauli.actionHom_ker_eq_innerHom_range`, `Pauli.quotientEquivSymplectic`, `Pauli.autEquivCoordinates` | An explicit symmetric-Weyl lift proves surjectivity and a splitting in odd dimension. These concern abstract scalar-fixing Pauli automorphisms, not an assumed equality with the circuit group. |
| Actual unitary matrix normalizers | `NormalizesPaulis`, `cliffordMatrixGroup`, `normalizerConjugationHom`, `cliffordSymplecticHom`, `mem_cliffordSymplecticHom_ker_iff` in `CliffordAction.lean` | Constructs conjugation from faithful complex matrices and proves that its symplectic kernel is exactly projective Pauli matrices. The full normalizer includes arbitrary unitary scalars; surjectivity and identification with the finitely generated exact circuit group remain unproved. |
| Figure 6; Lemmas 3.4–3.7 | `ABox.existsUnique_normalizer`, `existsUnique_oneQuditNormal`, `ZNormal.existsUnique_normalizer`, `XNormal.existsUnique_normalizer`, `existsUnique_pair_normalizer` in the normal-box modules | Concrete A/B/D/E words and intrinsic arbitrary-wire Z/X grammars; actual exponent actions and unique normalization, without a semantic-equality rewrite rule. |
| Proposition 3.8; repaired Appendix E induction | `WireSymplectic.restrict`, `WireSymplectic.lift_restrict`, `SymplecticNormalForm.existsUnique_equiv`, `SymplecticNormalForm.equivWireSymplectic` | The literal recursive A/B/D/E syntax gives each finite-field symplectic equivalence exactly once. Restriction is on exponent space, so no exact Pauli-phase factorization is assumed. |
| Lemma 3.9; normal-form counting | `ZNormal.card`, `XNormal.card`, `SymplecticNormalForm.card`, `symplecticGroup_card` in the counting modules | Counts the actual normal syntax and transports its bijection to the existing group: `d^(n^2) * product_(j=1..n) (d^(2*j)-1)`. This is not yet a cardinality theorem for the generated exact Clifford matrix group. |
| Abstract automorphism count | `scalarFixingAut_card` in `SymplecticCounting.lean` | Combines the explicit split exact sequence and the proved symplectic cardinality; it retains the distinction from generated Clifford matrices. |
| Normal-box coordinate correspondence | `wiresCoordinates`, `ZNormal.existsUnique_phaseNormalizer`, `existsUnique_phasePairNormalizer` in `NormalCoordinates.lean` | Linear coordinate equivalence preserves the existing `symplectic` form and exposes the checked normalizations directly on `PhaseSpace d n`. Complex-matrix box interpretation and rewrite derivations remain distinct. |
| Elementary symplectic gate actions | `localHadamard_preserves`, `localPhaseShear_preserves`, `localMultiplier_preserves`, `controlledPhase_preserves` | Algebraic phase-space actions. Their full correspondence with named-wire matrix conjugation is not yet a single established bridge theorem. |
| Definitions 2.29-2.31; circuit syntax | `Circuit.Gate`, `Circuit.denote`, `Circuit.Figure1Rule`, `Circuit.Derives` in `Circuit.lean` | Primitive words over `-omega,H,S,CZ`, exact matrix denotation, and all sixteen syntactic rule schemas with derived gates expanded. C3 uses `Fin d`, not a silently enlarged infinite family. |
| Named-wire placement and circuit unitarity | `Circuit.onWire_one`, `Circuit.onWire_mul`, `Circuit.onWire_adjoint`, `Circuit.onWire_unitary`, `Circuit.onWire_pow`, `Circuit.Gate.denote_unitary`, `Circuit.denote_unitary` | Placement laws and unitarity of every primitive circuit proved from matrix entries. |
| Full exact expanded soundness | `Circuit.structural_sound`, `Circuit.figure1_rule_sound`, `Circuit.figure1_sound` in `MultiplierSoundness.lean` | Proves every expanded Figure 1 rule and its contextual rewrite closure for arbitrary named wires in odd prime dimension. The Gauss-sign hypothesis of intermediate lemmas is discharged by `baseGaussSign_eq_one`; no additional hypothesis beyond the stated dimension conditions is required. |
| Section 2.3.2 rewriting infrastructure | `Presentation.sound_derives`, `Presentation.Derives.mono` | Explicit contextual closure of syntactic relations. |
| Pauli normalization relevant to §3.2 | `PauliRewrite.normalize`, `PauliRewrite.complete`, `PauliRewrite.derives_iff_matrix_eq` | A complete exact presentation of the ordinary omega-Pauli subgroup, using block X/Z powers and explicit phase relations. This is not the paper's sixteen-rule presentation, nor the full Clifford normal form. |
| Actual Figure 1 scalar fragment | `Circuit.scalar_normalize`, `Circuit.scalar_complete`, `Circuit.zero_wire_sound_and_complete` in `ScalarCompleteness.lean` | C0 gives actual rewrite normalization modulo `2*d`; exact scalar completeness holds at every arity, and full soundness/completeness holds at arity zero. No projective completeness is assumed. |
| Generic normalization/lifting architecture | `Presentation.complete_of_normal_forms`, `Presentation.exact_injective_of_projective_lifting` | Conditional infrastructure: rewrite normalization/uniqueness and the scalar-lifting condition are explicit hypotheses. These hypotheses have not been instantiated for Figure 1. |

## Derived gates: actual circuit-word identities

| Figure 2 / Appendix | Checked result | Remaining obligation |
|---|---|---|
| T2 / A.16: X | `X_derived_word`, `Circuit.denote_X`, `Circuit.denote_Xexp` | Exact matrix word and expanded arbitrary-wire denotation, including powers, checked. |
| T3 / A.15: Z | `Z_derived_word`, `Circuit.denote_Z`, `Circuit.denote_Zexp` | Exact matrix word and expanded arbitrary-wire denotation, including powers, checked. |
| T4 / A.20: SWAP | `SWAP_derived`, `Circuit.denote_SWAP`, `Circuit.denote_SWAP_basisMap` | Exact full word, including `lambda^2`, and its transport to arbitrary distinct named wires are proved. |
| T5 / A.18: CX | `CX_derived`, `Circuit.denote_CX`, `Circuit.denote_CX_basisMap` | Exact `H_target^3 CZ H_target` and arbitrary-wire transport are proved. |
| Remote CZ / A.22 | `remote_controlled_phase`, `Circuit.denote_CIZ` | Exact fully expanded `SWAP23 CZ12 SWAP23=CZ13` on arbitrary distinct named wires. |
| T1 / Lemma 2.14: multiplier | `multiplier_derived`, `baseGaussSign_eq_one`, `squareGaussSum_half`, `Circuit.denote_multiplier` | **Complete for odd primes.** Exact Legendre/Gauss evaluation, finite-field square-sign encoding, the displayed scalar correction, and arbitrary-wire expanded denotation are proved. |
| Lemma A.10: other determinants | `det_S_exact`, `det_S_three`, `det_CZ_eq_one` in `GateDeterminants.lean` | Exact phase-gate determinant is omega at dimension 3 and one at larger odd primes; controlled-Z determinant is one. |
| Lemma A.9: Fourier determinant | `det_fourierMatrix_vandermonde`, `fourierVandermonde_phase_sum`, `fourierSineProduct_pos`, `det_H_eq_one` in `GaussSign.lean` | The positive-real Vandermonde amplitude and unitarity determine `det(H)=1`; no Gauss-sign assumption is used. |

## All sixteen raw-matrix identities are checked

These declarations use the intended raw matrices and preserve every scalar:

| Rule | Declaration in `Relations.lean` |
|---|---|
| C0 | `C0_scalar` |
| C1 | `C1_phase_order` |
| C2 | `C2_hadamard_square` |
| C3 | `C3_multiplier_power` |
| C4 | `C4_multiplier_phase` |
| C5 | `C5_hadamard_phase` |
| C6 | `C6_controlled_phase_order` |
| C7 | `C7_swap_sq` |
| C8 | `C8_controlled_phase_commutes` |
| C9 | `C9_controlled_multiplier` |
| C10 | `C10_swap_phase` |
| C11 | `C11_swap_hadamard` |
| C12 | `C12_controlled_add_phase` |
| C13 | `C13_swap_braid` |
| C14 | `C14_swap_controlled_phase` |
| C15 | `C15_controlled_interaction` |

The raw-matrix table alone does **not** establish `Circuit.Figure1Sound`. That stronger theorem is now separately proved by `Circuit.figure1_sound`, using exact derived-word identities, named-wire transport, and contextual closure. None of these soundness results establishes positive-arity Figure 1 completeness.

## Explicit remaining source obligations

1. **Cyclotomic and scalar-group results:** Propositions 2.5-2.6, Lemma 2.16, and the generated-Clifford scalar characterization corresponding to Proposition 2.17 under the selected enlarged convention.
2. **Generated Clifford groups and quotient correspondence:** the actual unitary normalizer action and its projective Pauli kernel are proved, as is the split exact sequence for abstract scalar-fixing Pauli automorphisms. Remaining: realize all symplectic maps by the paper's generators, identify the generated exact group and its scalar subgroup, and establish the adapted Proposition 2.26/Theorem 2.27 for that group.
3. **Exact multiplier implementation: discharged.** `multiplier_derived` and `Circuit.denote_multiplier` prove Lemma 2.14 and its expanded primitive implementation, including the signed Gauss sum.
4. **Expanded-rule soundness: discharged.** `Circuit.figure1_sound` proves exact soundness for all arities. The relation between named-wire structural coherence and the paper's graphical embeddings remains a source-model obligation for presentation completeness.
5. **Section 3's exponent-level symplectic normal form and count: discharged.** Concrete A/B/D/E words, arbitrary-wire Z/X grammars, recursive Proposition 3.8, and cardinality Lemma 3.9 are proved and connected to the existing phase space. Remaining: complex-matrix/primitive-circuit interpretation of this normal-form grammar and its derivability from the presentation.
6. **Full Clifford matrix normal form:** combine the checked Pauli and concrete symplectic normal forms through their actual matrix/circuit implementations, then prove Definitions 3.12/Proposition 3.13 with the selected scalar extension and the corresponding adjusted cardinality. The abstract automorphism decomposition is proved, but is not substituted for that matrix-level assertion.
7. **Section 4.1 and Appendices D,F:** clean/dirty forms, the 42 local box-relation families, normalization by their generated rewrite congruence, and Theorem 4.4's derivation of those families from the 18 symplectic relations.
8. **Section 4.2's actual lifting:** instantiate Proposition 4.9 with the source's quotient rules, derive the necessary Pauli correction rules from the chosen presentation, then instantiate the exact scalar lifting with every signed correction. Generic lifting theorems remain conditional until these obligations are discharged.
9. **Theorem 4.10:** prove `Circuit.MainTheorem` from the checked source relations and explicit rewrite derivations for all positive arities. The arity-zero specialization is proved, but the quantified main theorem remains a target proposition only.

## Verification discipline

The `Audit.lean` check traverses every kernel-safe total project declaration, including private helpers, and all of its dependencies. Unsafe/partial compiler runtime artifacts are excluded only as roots; encountering one in a mathematical dependency chain is an error. The checker rejects all axioms except the three standard logical axioms. Scratch-file negative tests verified rejection of a custom axiom, a private custom axiom, a transitive external custom axiom, a `sorry` proof, and a `native_decide` proof. None of those probe declarations belongs to the delivered library.

The proofs use standard Lean/mathlib foundations. The inspected main matrix and faithfulness declarations report only `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or admitted paper theorem was introduced. The target `Circuit.MainTheorem` is not used as a hypothesis in the checked modules.

The modules named above were checked with Lean 4.19.0 and mathlib v4.19.0. A successful build confirms the declarations present in the repository; it does not change the pending obligations in this document into completed theorems. See `PAPER_AUDIT.md` for source convention repairs and the detailed theorem inventory.
