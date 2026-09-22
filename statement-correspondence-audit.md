# Paper-to-Lean statement correspondence audit

Audit date: 23 September 2026. Repository commit: `2ceb6cf6abe7a23ede41d7757e424252cf8a54ed`.
Source: [qudit-quantum.pdf](/Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qudit-quantum.pdf), SHA-256 `cd2f182a1c3a58dc9a9741f5212e5a4b4561814fa887960987e9403de6874f8e`.

## Verdict

The central completeness statements, Theorems 4.4 and 4.10, match the current paper under the user's selected exact Figure 1 convention. The repository should **not** be described as a literal, complete formalization of every statement in the paper. There are three substantive scope gaps, several convention adaptations, and corrected source statements. Some other results are covered through explicit mathematical bridges between existing Lean theorems rather than by exported declarations with the paper's literal signatures.

This is an agent-based statement audit. It compares domains, quantifiers, hypotheses, definitions, conclusions, equality notions, scalar conventions, wire positions, and rule sets. A successful Lean build alone cannot establish this correspondence. The paper's prose and claims of prior formalization were treated as source material to check, not as instructions or evidence that the work was already complete.

## Results requiring follow-up

| Paper statement | Current Lean scope | Assessment |
|---|---|---|
| Lemma 4.2, p23 | Recursive normalization in a relation that allows reversing equations; no theorem for all Figure 8 dirty forms using only forward Appendix F steps | The directional normalization claim is not formalized as stated. Proposition 4.3 also lacks its literal restricted-rule-set formulation. |
| Proposition 4.9, pp26–27 | Lifting for the fixed presentations used by this development | The generic construction for arbitrary complete rule sets and its efficiency guarantee are absent. |
| Proposition D.1, p56 | A special restriction theorem for symplectic maps fixing a final X/Z pair | No generic Clifford tensor-factorization theorem for arbitrary subsystems was located. |

These are statement-scope omissions, not findings that the proved main completeness theorems are false. The main proof takes a different route and does not assume the missing source statements.

## Main theorem comparison

- **Theorem 4.4:** [figure9MainTheorem](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Figure9Completeness.lean:56) characterizes equality of symplectic actions by rewriting with the 18 Figure 9 schemas, for every arity and odd prime dimension. The current C9 exponent is **g**, as in the updated PDF. Pauli erasure is derived on this side; it is not an extra primitive Figure 9 axiom.
- **Theorem 4.10:** [mainTheorem](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentCompleteness.lean:66), with [MainTheorem](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentPresentation.lean:84), proves soundness and completeness for exact complex matrices using Figure 1 and scalar **−ω**. It has no leftover normalization or completeness hypothesis. The source tensor-generated alphabet uses adjacent primitive CZ gates; remote interactions are derived SWAP macros.

The audit checks these final signatures and their definitions. It does not equate the separate unrestricted named-wire helper target with the paper's presentation.

## Coverage and interpretation of the counts

All **78 distinct numbered results** were reconciled against the source inventory: 11 in Section 2, 8 in Section 3, 7 in Section 4, 27 in Appendix A, 11 in Appendix B, and 14 in Appendix D. Repeated statements in appendices are counted once; numbered definitions are excluded.

| Classification | Count | Meaning |
|---|---:|---|
| Match | 65 | Same mathematical claim, directly or through a documented elementary/representation bridge. |
| Selected-convention adaptation | 5 | The −ω convention changes the exact group, scalar data, or quotient packaging. |
| Corrected statement | 5 | Lean follows a repaired domain, phase, identity seed, or equality interpretation. |
| Specialization / weaker result | 2 | A related theorem is proved, but part of the source's generality or directional assertion is absent. |
| Missing | 1 | No matching theorem was located. |

“65 matches” is **not** a claim that 65 dedicated paper-shaped declarations were found. For example, Lemmas 3.4–3.8 and 3.11 use formal coordinate/compilation bridges; Lemma 4.5 is a kernel/coset consequence; B.5–B.7 follow by the explicit diagonal and quadratic calculation documented in the foundations addendum. These assembled wrappers were not added or compiled during this audit. The correspondence judgment is reviewer evidence, not itself a formal certificate.

Additional comparisons cover all **16 Figure 1 schemas**, **18 Figure 9 schemas**, and **42 Appendix F branches**. The schema and branch ledgers record substitutions, order reversal, nonzero hypotheses, and allowed wire support. In Figure 20, a residual-order difference is justified by existing syntactic commutation and replay theorems, rather than by an unsupported appeal to semantic equality.

## Source discrepancies and convention changes

- **Selected scalar convention:** Section 2's ω-only group differs from the selected −ω-generated group. Results 2.16, 2.17, 2.26, 2.27 and 3.13 require the stated adaptation. The selected exact group has an extra sign, so the unnumbered cardinality in Remark 3.14 changes by a factor of two. This is an authorized convention choice, not a missing proof.
- **Proposition 4.8:** The printed Pauli-completeness condition includes phase-free commutation. Exact Figure 1 cannot yield `ZX = XZ`; its exact identity retains ω. Lean explicitly supplies a separate projective relation that discards scalars.
- **Proposition 4.3:** The printed identity seed uses `E_(d−1)` where the given box definition requires `E_0`. Lean uses `E_0`. Its normalizer also does not expose the proposition as a standalone theorem using only the 42 box rules plus that identity seed.
- **Lemma B.11:** The exact displayed SWAP decomposition lacks its scalar factor; Lean retains the phase. The phase-corrected version elsewhere in the paper matches.
- **Proposition 2.6 and Lemma A.1:** Lean uses positive root order and positive modulus. The printed domains omit these conditions. These are domain repairs, not substantive gaps in the intended mathematics.
- **Appendix C:** The normal-form reviewer identified 17 erroneous action cells in Figures 10–12. Lean follows the concrete Figure 6 definitions. For example, for `a ≠ 0`, `B_(a,b)` sends `X^a Z^b ⊗ I` to `I ⊗ Z^a` up to phase, whereas Figure 11 prints `I ⊗ Z`. Taking `d=5, a=2` distinguishes them even after discarding scalar phase. This follows directly by composing the Figure 6 shear, Fourier, controlled-addition, and SWAP actions, and agrees with [bAction_nonzero](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalLayers.lean:74).
- **Other supporting prose/diagrams:** The section reviews document stale remote-gate definitions in Eqs. 42–43, the overly strong same-linear-map assertion on p18, the missing phase correction in Appendix E's exact factorization Eq. 111, and two reduction-diagram label slips. These are separately recorded and do not inflate the count of 78 numbered results.

## Review organization and evidence boundaries

Two fresh-context reviewers independently covered foundations and normal forms. The coordinating reviewer covered Section 4, Appendix B, Figures 1/9, and all 42 Appendix F branches. Cross-review resolved B.5–B.7 and Figure 20. A third fresh-context reviewer challenged the proposed missing-statement findings and checked the main theorem signatures; its separate report is linked below.

The challenger confirmed all three scope omissions and both main-theorem matches. It also independently checked a simple source counterexample: Figure 10 says `A_01` sends `X` to `XZ^(-1)`, but Figure 6 defines `A_01=M_1=I`. The discrepancy persists even up to scalar phase. The challenger's bounded pass did not separately recheck all 17 Appendix C cells; that complete inventory belongs to the normal-form reviewer.

The review inspected the exact updated PDF, rendered diagrams, matching TeX locations, and actual Lean definitions and theorem signatures. It did not rely on declaration names or comments alone. The repository and paper were kept read-only. No new build or proof-wrapper compilation was performed in this statement audit; the previous clean build concerns the same unchanged commit and answers a separate proof-checking question.

An agent can still overlook a mismatch. The concrete ledger, source locations, explicit differences, and independent challenge are the evidence supplied here; agent agreement is not a mathematical proof that the translation is faithful.

## Detailed evidence

- [Foundations: Section 2 and Appendix A, plus B.5–B.7/Figure 20 cross-review](/Users/sarahli/.codex/.chatgpt-projects/g-p-6a82bb1224148191bae14c66378ffbb3/output/review/swarm-2026-09-23/foundations.md)
- [Normal forms: Section 3 and Appendices C–E](/Users/sarahli/.codex/.chatgpt-projects/g-p-6a82bb1224148191bae14c66378ffbb3/output/review/swarm-2026-09-23/normal-forms.md)
- [Completeness: Section 4 and Appendix B](/Users/sarahli/.codex/.chatgpt-projects/g-p-6a82bb1224148191bae14c66378ffbb3/output/review/swarm-2026-09-23/completeness.md)
- [Independent challenge of the major findings](/Users/sarahli/.codex/.chatgpt-projects/g-p-6a82bb1224148191bae14c66378ffbb3/output/review/swarm-2026-09-23/challenger.md)
- [All 34 Figure 1/9 schemas](/Users/sarahli/.codex/.chatgpt-projects/g-p-6a82bb1224148191bae14c66378ffbb3/output/review/swarm-2026-09-23/rule-schemas.md)
- [All 42 Appendix F branches](/Users/sarahli/.codex/.chatgpt-projects/g-p-6a82bb1224148191bae14c66378ffbb3/output/review/swarm-2026-09-23/box-relations.md)
- [Combined machine-readable ledger](/Users/sarahli/.codex/.chatgpt-projects/g-p-6a82bb1224148191bae14c66378ffbb3/output/review/swarm-2026-09-23/statement-correspondence-audit.json)

## Complete numbered-result ledger

### Proposition 2.5 — match

PDF p. 8. hadamard_scale_mem_coefficientRing states exactly (lambda d * sqrt d)^(-1) in the concrete subring closure of {omega,1/d}. The normalization lambda is the same complex exponential as the paper.

Scope: d:Nat, NeZero d, Fact d.Prime, hd:Odd d. No unproved Gauss-value hypothesis in this final signature. Repeated on paper p34, counted once.

Lean: [CyclotomicScalars.lean:239](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CyclotomicScalars.lean:239), [CyclotomicScalars.lean:262](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CyclotomicScalars.lean:262), [Gates.lean:262](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:262).

Source location: scripts/2-foundation.tex:63-67; label lem:lambda-in-ring.

### Proposition 2.6 — corrected statement

PDF p. 8. coefficientRing_torsion_iff classifies ring elements of finite positive order as powers of -omega. In odd dimension this is precisely {+/-omega^t}, so the mathematical classification matches the standard meaning. However the paper explicitly defines N to include zero and then says c^n=1 for some n in N; taken literally that definition includes every c, and cannot be the definition used by Lean.

Scope: Lean uses IsOfFinOrder, whose mathlib equivalence requires an exponent >0. This repairs a source-definition boundary, not a Lean error. The theorem needs only d:Nat, NeZero d and Odd d; hence is at least as general as the paper in valid positive dimensions.

Lean: [CyclotomicScalars.lean:271](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CyclotomicScalars.lean:271), [RootOfUnity.lean:73](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:73), [RootOfUnity.lean:77](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:77), [RootOfUnity.lean:80](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:80).

Source location: scripts/2-foundation.tex:13-16,69-72; label lem:roots-of-unity.

### Proposition 2.12 — match

PDF p. 10. H_sq states H*H = lambda^(-2) times the basis permutation j -> -j. The matrix entry definition of basisMap gives exactly the displayed action on every computational basis state.

Scope: Only nonzero natural d is needed in Lean, stronger than the odd-prime paper scope; no phase quotient. Repeated on p34, counted once.

Lean: [Gates.lean:268](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:268), [Gates.lean:18](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:18).

Source location: scripts/2-foundation.tex:169-173; label prop:hsquared.

### Lemma 2.14 — match

PDF p. 10. multiplier_derived has the exact Legendre factor and omega^((-a^2+4a-2)/(8a)), multiplying Z^((1-a)/(2a)) X^((1-a)/2) S^(a^-1) H S^a H S^(a^-1) H, and concludes the raw matrix |x> -> |ax>. complexQuadraticChar_eq_legendreSym supplies the explicit character identification. denote_multiplier also proves the fully expanded primitive word has that same exact matrix.

Scope: All units a in ZMod d, equivalent to all nonzero field elements for prime d; d odd prime. The final theorems are unconditional on Gauss evaluation. Raw-multiplier membership in the paper's narrower group is a separate inconsistent definition, not part of this exact matrix identity.

Lean: [GaussSign.lean:285](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GaussSign.lean:285), [MultiplierDerivation.lean:162](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierDerivation.lean:162), [GaussEvaluation.lean:41](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GaussEvaluation.lean:41), [MultiplierSoundness.lean:55](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierSoundness.lean:55), [Circuit.lean:106](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:106).

Source location: scripts/2-foundation.tex:184-188; repeated scripts/appendix/sectiontwoproofs.tex:610 onward; equation (37) at line520.

### Lemma 2.16 — selected-convention adaptation

PDF p. 11. denote_mem_coefficientRing proves every actual primitive-word matrix entry lies in Z[1/d,omega]. mem_generated_iff transfers this to the matrix subgroup generated by -omega,H,S,CZ. Unitarity is independently present. This proves the analogous assertion for the enlarged selected group, and implies the narrower paper assertion after embedding omega as (-omega)^(d+1).

Scope: All n:Nat, including n=0; d odd prime. Lean's displayed coefficient theorem is word-indexed rather than a literal subgroup-containment theorem, but the checked word/subgroup equivalence bridges that difference. The group parameter is not silently identified with Definition 2.11.

Lean: [CyclotomicScalars.lean:316](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CyclotomicScalars.lean:316), [GeneratedClifford.lean:42](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedClifford.lean:42), [CircuitSemantics.lean:117](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitSemantics.lean:117).

Source location: scripts/2-foundation.tex:242-249; label lem:representable.

### Proposition 2.17 — selected-convention adaptation

PDF p. 11. The source says the omega-only Clifford group has exactly d scalar phases. Lean instead characterizes the actual -omega-generated group: scalar_circuit_iff says a scalar is realized iff c^(2*d)=1, and generated_scalar_iff identifies group scalars as powers of -omega. This is not the literal Proposition 2.17; -I is an explicit witness to the difference.

Scope: All n:Nat, including n=0, and all odd prime d. This is the user-selected enlargement, not a missing proof of the 2d-phase version. No separate theorem for the source's narrower omega-only Clifford subgroup was identified.

Lean: [CyclotomicScalars.lean:226](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CyclotomicScalars.lean:226), [GeneratedScalarKernel.lean:15](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedScalarKernel.lean:15), [GeneratedScalarKernel.lean:33](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedScalarKernel.lean:33), [GeneratedClifford.lean:18](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedClifford.lean:18), [RootOfUnity.lean:77](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:77).

Source location: scripts/2-foundation.tex:252-276; label lem:qupit-Clifford-phase.

### Proposition 2.21 — match

PDF p. 12. pauli_centralizer states that an actual complex matrix commutes with all faithfully represented ordinary Paulis iff it is scalar. For the paper's unitary C, CPC-adjoint=P is equivalent to CP=PC, giving its exact conclusion. This is stronger than a merely abstract-coordinate assertion.

Scope: All n, nonzero d; unitarity is needed only for the elementary conversion from the paper's conjugation hypothesis. The centralizer theorem itself quantifies arbitrary matrices and needs no primality.

Lean: [Centralizer.lean:54](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Centralizer.lean:54), [Centralizer.lean:71](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Centralizer.lean:71), [PauliRepresentation.lean:23](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliRepresentation.lean:23), [PauliRepresentation.lean:58](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliRepresentation.lean:58).

Source location: scripts/2-foundation.tex:308-314; label prop:scalars.

### Lemma 2.23 — match

PDF p. 13. The four explicit adjoint identities are HXH*=Z, HZH*=shift(-1), SXS*=XZ, SZS*=Z. shift(-1) is the inverse of X by shift_add. Gate.denote_normalizes establishes normalizer membership for H and S on arbitrary placed wires, so the membership claim is not inferred only from an abstract action.

Scope: Nonzero d for H/Z identities; Odd d for S/X and normalizer membership. All are valid over the paper's odd-prime domain; no extra input assumption about normalizing Paulis.

Lean: [Gates.lean:420](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:420), [Gates.lean:423](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:423), [Gates.lean:426](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:426), [Gates.lean:429](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:429), [CircuitPauliAction.lean:161](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:161).

Source location: scripts/2-foundation.tex:332-340; label lem:automorphism; PDF equation (10).

### Lemma 2.24 — match

PDF p. 13. The matrix pushing equalities give CZ(X tensor I)=(X tensor Z)CZ, CZ(I tensor X)=(Z tensor X)CZ, and preservation of both Z generators. Unitarity converts pushing to the diagram's conjugation. The last two displayed cancellation actions follow by multiplying these generator actions. Normalizer membership is separately proved.

Scope: The four matrix identities and unitarity hold for every nonzero d; the general primitive normalizer theorem uses Odd d. Diagram visually checked at PDF p13.

Lean: [Gates.lean:205](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:205), [Gates.lean:212](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:212), [Gates.lean:219](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:219), [Gates.lean:225](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:225), [Gates.lean:358](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:358), [CircuitPauliAction.lean:161](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:161).

Source location: scripts/2-foundation.tex:344-351; label lem:automorphism-CZ; PDF equation (11).

### Proposition 2.26 — selected-convention adaptation

PDF p. 14. The actual quotient theorem is generatedCliffordGroup / range(signedPauliToGenerated) isomorphic as a group to symplecticGroup. Its denominator contains the extra sign required by the selected scalar convention. This is not Cfig divided by the source's ordinary Pauli group; that denominator would leave an extra central sign. Kernel identification and surjectivity are proved for concrete matrices.

Scope: Every n and odd prime d. Symplectic coordinates are (z,x), exactly the source ordering. ExactNormalForm's comment calls this Theorem2.27, but its actual mathematical content corresponds to Proposition2.26; audit follows the signature, not comment numbering.

Lean: [ExactNormalForm.lean:116](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExactNormalForm.lean:116), [GeneratedScalarKernel.lean:88](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedScalarKernel.lean:88), [GeneratedRealization.lean:16](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedRealization.lean:16), [GeneratedClifford.lean:18](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedClifford.lean:18), [Symplectic.lean:18](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Symplectic.lean:18).

Source location: scripts/2-foundation.tex:382-384 (unlabelled proposition).

### Theorem 2.27 — selected-convention adaptation

PDF p. 14. The matrix generated group modulo its scalar-action kernel is group-isomorphic to PhaseSpace semidirect symplecticGroup, with the usual linear action. The paper writes Sp semidirect-left PhaseSpace; the reversed display order is the standard equivalent notation for a normal translation subgroup acted on by Sp. The real adaptation is quotienting the selected enlarged group by all 2d scalar phases rather than quotienting the source omega-only group by its d phases.

Scope: Every n and odd prime d; no unproved realization/surjectivity hypothesis in the final equivalence. The scalar kernel is independently identified, so this is not just defining an abstract Clifford model to be a semidirect product.

Lean: [CliffordSemidirect.lean:89](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CliffordSemidirect.lean:89), [CliffordSemidirect.lean:48](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CliffordSemidirect.lean:48), [CliffordSemidirect.lean:19](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CliffordSemidirect.lean:19), [GeneratedQuotients.lean:18](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedQuotients.lean:18), [GeneratedScalarKernel.lean:33](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedScalarKernel.lean:33).

Source location: scripts/2-foundation.tex:387-390; label thm:semidirect.

### Lemma 3.4 — match

PDF p. 19. The full multiwire theorem quantifies every nonzero exponent vector and asserts unique A/B-grammar ZNormal data sending it to first-wire Z. Equality of exponents is exactly Pauli equality up to central phase; the concrete compiler and Pauli-conjugation theorems connect that action to matrices. This is not merely the one-qudit ABox lemma.

Scope: n+1 means every positive register size; the paper non-scalar premise is impossible on zero wires. The literal Pauli-matrix ∃! statement is obtained by composing listed lemmas, not by one exported theorem of that exact signature. Paper globally assumes odd prime dimension. Algebraic normal-box theorems work over a field, often more generally than the paper. Specialization K=ZMod d and the exact conjugation bridge require prime d and Odd d. Wire pairs use (z,x), so label (a,b) is represented as (b,a); there is no X/Z reversal.

Lean: [ZNormal.lean:227](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ZNormal.lean:227), [NormalCoordinates.lean:83](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCoordinates.lean:83), [NormalCircuit.lean:137](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:137), [NormalCircuit.lean:150](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:150), [CircuitPauliAction.lean:181](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:181), [CircuitPauliAction.lean:200](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:200), [Pauli.lean:159](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Pauli.lean:159).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:150; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qupit.sty:147; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/normal-form.tex:4.

### Lemma 3.5 — match

PDF p. 19. Unique D/E-grammar XNormal sends the input to last-wire X. Lean premise (v 0).2=1 is exactly first-wire Z omega-commuting with the Pauli, using the (z,x) symplectic convention.

Scope: Every positive n; no restriction on other exponents. The Pauli-matrix formulation is a corollary through the listed bridges rather than an identically packaged theorem. Paper globally assumes odd prime dimension. Algebraic normal-box theorems work over a field, often more generally than the paper. Specialization K=ZMod d and the exact conjugation bridge require prime d and Odd d. Wire pairs use (z,x), so label (a,b) is represented as (b,a); there is no X/Z reversal.

Lean: [XNormal.lean:173](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/XNormal.lean:173), [ZNormal.lean:46](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ZNormal.lean:46), [NormalCircuit.lean:137](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:137), [NormalCircuit.lean:150](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:150), [CircuitPauliAction.lean:181](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:181), [CircuitPauliAction.lean:200](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:200), [Pauli.lean:159](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Pauli.lean:159).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:157; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qupit.sty:150; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/normal-form.tex:31.

### Lemma 3.6 — match

PDF p. 19. Every literal XNormal grammar value maps first-wire Z to last-wire Z. The universal quantifier includes all D labels and the final E label. Concrete compilation and exact Pauli conjugation recover the paper up-to-phase action.

Scope: No extra input hypothesis; positive arity is implicit in the paper Z on first/last wire. Paper globally assumes odd prime dimension. Algebraic normal-box theorems work over a field, often more generally than the paper. Specialization K=ZMod d and the exact conjugation bridge require prime d and Odd d. Wire pairs use (z,x), so label (a,b) is represented as (b,a); there is no X/Z reversal.

Lean: [XNormal.lean:61](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/XNormal.lean:61), [NormalCircuit.lean:150](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:150), [CircuitPauliAction.lean:200](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:200).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:164; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qupit.sty:153; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/normal-form.tex:56.

### Lemma 3.7 — match

PDF p. 20. The theorem asserts ∃! over a pair ZNormal × XNormal with both specified outputs: last Z and last X. symplectic p q=1 is the exponent form of PQ=omega QP. Both normal components are jointly unique, not just existence of a composite transformation.

Scope: Composition is X.action (Z.action p), matching matrix W_X W_Z. One theorem covers all positive arities, all nontrivial omega-commuting pairs. Paper globally assumes odd prime dimension. Algebraic normal-box theorems work over a field, often more generally than the paper. Specialization K=ZMod d and the exact conjugation bridge require prime d and Odd d. Wire pairs use (z,x), so label (a,b) is represented as (b,a); there is no X/Z reversal.

Lean: [XNormal.lean:184](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/XNormal.lean:184), [NormalCoordinates.lean:99](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCoordinates.lean:99), [NormalCircuit.lean:137](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:137), [NormalCircuit.lean:150](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:150), [CircuitPauliAction.lean:181](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:181), [CircuitPauliAction.lean:200](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:200), [Pauli.lean:159](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Pauli.lean:159).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:171; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qupit.sty:156; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/normal-form.tex:73.

### Proposition 3.8 — match

PDF p. 20. The exported normal-form theorem is ∃! concrete recursive normal data for each WireSymplectic map. PauliAutomorphisms sends every scalar-fixing Pauli automorphism to that symplectic group; action_coords identifies all Pauli inputs. Together with compilation this is the paper proposition, including uniqueness. There is no single exported signature quantifying phi and every Pauli P exactly as the prose does.

Scope: FixesScalars quantifies all scalar powers; paper phi(omega)=omega is equivalent for a group automorphism. n=0 is included. The proof uses phase space, repairing the exact-factorization step in Appendix E without changing this up-to-phase proposition. Paper globally assumes odd prime dimension. Algebraic normal-box theorems work over a field, often more generally than the paper. Specialization K=ZMod d and the exact conjugation bridge require prime d and Odd d. Wire pairs use (z,x), so label (a,b) is represented as (b,a); there is no X/Z reversal.

Lean: [SymplecticNormalForm.lean:133](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticNormalForm.lean:133), [PauliAutomorphisms.lean:26](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliAutomorphisms.lean:26), [PauliAutomorphisms.lean:46](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliAutomorphisms.lean:46), [PauliAutomorphisms.lean:102](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliAutomorphisms.lean:102), [SymplecticCoordinates.lean:35](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticCoordinates.lean:35), [NormalCircuit.lean:174](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:174), [CircuitPauliAction.lean:200](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:200).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:178; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qupit.sty:159; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/normal-form.tex:100.

### Lemma 3.9 — match

PDF p. 20. Nat.card(symplecticGroup d n)=d^(n^2) product_{i=0}^{n-1}(d^(2(i+1))-1), exactly the paper product because sum_{k=1}^n(2k-1)=n^2. Counts the actual recursively defined normal grammar via an established equivalence, not an assumed cardinality.

Scope: All n including zero, prime d; oddness not needed for the group count. Lean is more general at this algebraic level.

Lean: [SymplecticCounting.lean:69](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticCounting.lean:69), [SymplecticCounting.lean:46](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticCounting.lean:46), [NormalCounting.lean:47](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCounting.lean:47), [NormalCounting.lean:55](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCounting.lean:55).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:187; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/qupit.sty:162; /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/normal-form.tex:171.

### Lemma 3.11 — match

PDF p. 20. Ordinary Pauli tuples have unique phase,x,z coordinates, and phase-zero X/Z words compile to their actual matrices. Dropping the phase coordinate gives the unique paper Pauli normal form up to phase. Source diagram applies Z then X; Lean list allX++allZ is in matrix order and therefore the same order.

Scope: No standalone exported ∃! phase-free Pauli circuit theorem was located. The claim is an immediate coordinate/representation corollary of the listed declarations; the existing matrix uniqueness theorem retains the phase coordinate. All n; exact compilation requires odd d.

Lean: [Pauli.lean:121](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Pauli.lean:121), [Pauli.lean:125](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Pauli.lean:125), [Pauli.lean:159](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Pauli.lean:159), [PauliRepresentation.lean:92](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliRepresentation.lean:92), [PauliCircuit.lean:46](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliCircuit.lean:46), [PauliCircuit.lean:50](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliCircuit.lean:50), [PauliCircuit.lean:94](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliCircuit.lean:94).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:215.

### Proposition 3.13 — selected-convention adaptation

PDF p. 21. The named counterpart proves unique exact data SignedPauli × SymplecticNormalForm for every actual generated Clifford matrix, with exact equality. The paper instead quantifies the phase-free normal circuit N_S;N_P with projective equality. Erasing sign and scalar coordinates yields the intended projective normal form, but this is not the literal signature and is not packaged separately.

Scope: Selected -omega convention enlarges exact scalar data by an independent sign. Do not equate unique exact signed data with the paper projective normal-circuit statement without explicitly taking its scalar quotient. Matrix order signedPauliWord++N.toWord implements N_S followed by N_P.

Lean: [ExactNormalForm.lean:19](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExactNormalForm.lean:19), [ExactNormalForm.lean:23](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExactNormalForm.lean:23), [ExactNormalForm.lean:56](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExactNormalForm.lean:56), [ExactNormalForm.lean:68](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExactNormalForm.lean:68), [ExactNormalForm.lean:93](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExactNormalForm.lean:93), [PauliCircuit.lean:101](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliCircuit.lean:101).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/3-assemble.tex:245.

### Lemma 4.2 — specialization/weaker result

PDF p. 23. The source requires a finite normalization of arbitrary Figure8 dirty normal forms using AppendixF box rules left-to-right only. Lean has typed intermediate residual words and recursive normalization in a symmetric contextual relation; no explicit directed box-step relation or full Figure8 dirty-form statement was found. This is not the same directional theorem.

Scope: The source asserts existence of a finite forward-only rewrite sequence, not termination of every possible rewrite strategy. Termination of the Lean proof recursion does not by itself establish the required forward-only sequence.

Evidence type: related result.

Lean: [NormalSweepSyntax.lean:24](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalSweepSyntax.lean:24), [AdjacentNormalFormSweeps.lean:22](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentNormalFormSweeps.lean:22), [AdjacentCompleteness.lean:33](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentCompleteness.lean:33), [Presentation.lean:23](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Presentation.lean:23).

Source location: scripts/4-completeness.tex:65.

### Proposition 4.3 — corrected statement

PDF p. 23. Normalization existence is proved for the adjacent source alphabet. The source identity seed Eq12 uses E_(d-1), whereas E_b=S^(-b) requires E_0. Lean uses the corrected seed. Its theorem concludes derivability in the erased presentation, not a standalone relation generated only by the 42 box schemas and printed Eq12.

Scope: Source inputs H,S,CZ are a subset of the formal alphabet; additional scalar inputs are handled by erasure.

Evidence type: related result.

Lean: [AdjacentCompleteness.lean:33](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentCompleteness.lean:33), [AdjacentNormalIdentity.lean:18](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentNormalIdentity.lean:18), [NormalCircuit.lean:24](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalCircuit.lean:24).

Source location: scripts/4-completeness.tex:72.

### Theorem 4.4 — match

PDF p. 24. Same sound/complete symplectic presentation on scalar-free adjacent H/S/CZ circuits. Derived macros are expanded, C9 uses current g, Pauli deletion is derived rather than assumed. eraseScalar is identity on the source scalar-free alphabet.

Scope: Odd prime d, arbitrary n, g a unit of order d-1. Scalars retained as literal letters are intentionally outside this Figure9 alphabet.

Evidence type: direct.

Lean: [Figure9Completeness.lean:56](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Figure9Completeness.lean:56), [Figure9Syntax.lean:104](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Figure9Syntax.lean:104), [Figure9BoxCases.lean:19](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Figure9BoxCases.lean:19).

Source location: scripts/4-completeness.tex:103.

### Lemma 4.5 — match

PDF p. 25. The actual generated-matrix symplectic kernel is the signed Pauli subgroup; apply it to U*V^-1. Faithful Pauli coordinates identify the correction uniquely modulo its scalar coordinate. This is the source statement as a kernel/coset corollary, not a dedicated lemma4.5 wrapper.

Scope: Use matrix order P*V, corresponding to temporal V;P. No rewrite-completeness assumption is necessary.

Evidence type: corollary.

Lean: [GeneratedScalarKernel.lean:88](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GeneratedScalarKernel.lean:88), [CliffordAction.lean:284](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CliffordAction.lean:284), [PauliAutomorphisms.lean:196](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliAutomorphisms.lean:196), [PauliRepresentation.lean:82](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliRepresentation.lean:82).

Source location: scripts/4-completeness.tex:127.

### Proposition 4.8 — corrected statement

PDF p. 26. The displayed definition of Pauli completeness requires phase-discarded ZX=XZ. Exact Figure1 rewriting cannot derive this because ZX=omega*XZ. Lean proves exact phase-corrected identities, with scalar-deletion added in a separate projective relation to obtain the intended phase-discarded rules. Do not call this the literal same exact rewrite relation.

Scope: Exact and projective relations are explicitly separated.

Evidence type: related result.

Lean: [ProjectiveRewrites.lean:20](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ProjectiveRewrites.lean:20), [PauliWeylRewrites.lean:334](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/PauliWeylRewrites.lean:334), [DerivedPauliRewrites.lean:146](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/DerivedPauliRewrites.lean:146), [TwoWirePauliRewrites.lean:134](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/TwoWirePauliRewrites.lean:134), [Gates.lean:90](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:90).

Source location: scripts/4-completeness.tex:149.

### Proposition 4.9 — specialization/weaker result

PDF p. 26. Source quantifies over arbitrary complete Rs and Pauli-complete Rp and constructs corrected Rs efficiently. Lean proves lifting for fixed presentations; its generic injectivity lemma assumes lifting. No arbitrary rule-set construction or efficiency guarantee was located.

Scope: A correct fixed application does not establish the generic proposition.

Evidence type: related result.

Lean: [AdjacentPauliLifting.lean:34](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentPauliLifting.lean:34), [AdjacentPauliLifting.lean:70](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentPauliLifting.lean:70), [ProjectiveRewrites.lean:157](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ProjectiveRewrites.lean:157), [Presentation.lean:125](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Presentation.lean:125).

Source location: scripts/4-completeness.tex:186.

### Theorem 4.10 — match

PDF p. 27. Same exact soundness/completeness claim for Figure1 tensor-generated circuits with the selected -omega scalar. Conclusions use actual full complex matrix equality and syntactic contextual rewriting. Remote CZ is the source SWAP macro, not an extra primitive.

Scope: Odd prime d, arbitrary n, g of order d-1; no normalization/completeness premise. Match is to Figure1 theorem under the user-selected convention, not contradictory omega-only surrounding definitions.

Evidence type: direct.

Lean: [AdjacentCompleteness.lean:66](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentCompleteness.lean:66), [AdjacentPresentation.lean:78](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentPresentation.lean:78), [Circuit.lean:59](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:59), [Circuit.lean:143](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:143).

Source location: scripts/4-completeness.tex:204.

### Lemma A.1 — corrected statement

PDF p. 32. phase_sum gives character orthogonality for every nonzero natural modulus d and every residue a: the sum is d when a=0 and zero otherwise. The source writes k,n in Z without n>0, despite the range 0..n-1 and primitive n-th root. Lean supplies the meaningful positive-modulus formulation, including composite n; all integer k are represented by residues.

Scope: No primality or oddness restriction. Positivity of n is made explicit by Nat plus NeZero. It is not an exact transcription of the printed unrestricted integer n domain.

Lean: [RootOfUnity.lean:59](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:59), [RootOfUnity.lean:67](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:67), [RootOfUnity.lean:86](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:86).

Source location: scripts/appendix/sectiontwoproofs.tex:11-21; label lem:summation.

### Lemma A.2 — match

PDF p. 32. X_pow_dimension and Z_pow_dimension state the two exact matrix equalities X^d=1 and Z^d=1.

Scope: d:Nat with NeZero d, stronger than paper scope; both conjuncts checked.

Lean: [Gates.lean:74](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:74), [Gates.lean:76](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:76).

Source location: scripts/appendix/sectiontwoproofs.tex:37-40; label lem:Pauli-order.

### Lemma A.3 — match

PDF p. 32. ZX_eq_omega_XZ states ZX=omega*(XZ). Right multiplying by Z-adjoint X-adjoint and applying the separately proved unitarity of X,Z yields exactly ZXZ-adjoint X-adjoint=omega I. This is an elementary equivalent matrix form, not a separately named commutator theorem.

Scope: Every nonzero d; all scalar factors retained.

Lean: [Gates.lean:90](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:90), [Gates.lean:349](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:349), [Gates.lean:352](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:352).

Source location: scripts/appendix/sectiontwoproofs.tex:48-51; label lem:omega.

### Lemma A.4 — match

PDF p. 32. shift_pow and clock_pow prove the natural-power versions; shift_add and clock_add give the all-residue additive laws and show shift(-a),clock(-a) are the inverses. Thus the integer-power actions follow by splitting k into nonnegative and negative cases and interpreting integer powers in the unitary group. There is no dedicated integer-power wrapper, but no additional mathematical assumption or substantive theorem is required.

Scope: The stated shift_pow/clock_pow signatures use n:Nat, so they should not individually be advertised as literal all-integer signatures. Coverage of k:Int uses the inspected inverse/additive identities. Nonzero d suffices.

Lean: [Gates.lean:64](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:64), [Gates.lean:69](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:69), [Gates.lean:52](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:52), [Gates.lean:61](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:61), [Gates.lean:349](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:349), [Gates.lean:352](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:352).

Source location: scripts/appendix/sectiontwoproofs.tex:60-63; label lem:X-Z-copy.

### Lemma A.5 — match

PDF p. 33. clock_shift proves Z^a X^b=omega^(ab) X^b Z^a for arbitrary residues. Combining the all-residue inverse laws with unitarity gives both conjugation equations in A.5, including the minus sign in X^b Z^a X^(-b)=omega^(-ab) Z^a.

Scope: All residues a,b, including zero, and every nonzero d. Covered by equivalent matrix multiplication identities rather than a paired theorem named A.5.

Lean: [Gates.lean:79](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:79), [Gates.lean:52](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:52), [Gates.lean:61](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:61), [Gates.lean:320](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:320), [Gates.lean:337](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:337).

Source location: scripts/appendix/sectiontwoproofs.tex:73-76; label lem:anticommutation.

### Lemma A.7 — match

PDF p. 34. lambda_sq proves the stronger exact identity lambda^2=(-1)^((d-1)/2); squaring gives lambda^4=1. The latter also appears explicitly as a local theorem h_l in normalized_baseGaussSum.

Scope: d nonzero and odd; no separate top-level lambda_pow_four declaration. The conclusion follows by squaring an inspected theorem, with no missing number-theory input.

Lean: [Gates.lean:301](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:301), [GaussEvaluation.lean:276](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GaussEvaluation.lean:276).

Source location: scripts/appendix/sectiontwoproofs.tex:188-191; label lem:order-lambda-d.

### Corollary A.8 — match

PDF p. 35. H_pow_four states H d ^ 4 = 1 as an exact complex matrix identity.

Scope: Every nonzero odd d, so in particular every source odd prime.

Lean: [Gates.lean:409](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:409).

Source location: scripts/appendix/sectiontwoproofs.tex:203-206; label cor:orderh.

### Lemma A.9 — match

PDF p. 35. det_H_eq_one states det(H d)=1 for the same lambda-normalized complex Fourier matrix.

Scope: Fact d.Prime and hd:Odd d, matching source global scope. No determinant or Gauss-sign premise in this final signature.

Lean: [GaussSign.lean:254](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GaussSign.lean:254), [Gates.lean:265](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:265).

Source location: scripts/appendix/sectiontwoproofs.tex:233-236; label lem:det-H.

### Lemma A.10 — match

PDF p. 36. det_S_exact states det S = if d=3 then omega else 1; det_CZ_eq_one states det CZ=1. Both source branches are retained, including the exceptional qutrit determinant.

Scope: Fact d.Prime and Odd d; the else branch is exactly d>=5 under these hypotheses.

Lean: [GateDeterminants.lean:47](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GateDeterminants.lean:47), [GateDeterminants.lean:58](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GateDeterminants.lean:58).

Source location: scripts/appendix/sectiontwoproofs.tex:331-335; label lem:Clifford-syllable-determinant.

### Lemma A.11 — match

PDF p. 37. phasePower_nat identifies S^k with the diagonal phase d ((k mod d)*quadratic(j)); taking the natural representative of g gives precisely omega^(g*j*(j-1)/2).

Scope: The theorem handles all natural k and hence every residue, including the paper's nonzero residues. Division by 2 agrees because source d is odd.

Lean: [Relations.lean:41](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:41), [Relations.lean:51](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:51), [Gates.lean:153](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:153).

Source location: scripts/appendix/sectiontwoproofs.tex:383-386; label lem:multiple-s.

### Lemma A.12 — match

PDF p. 37. CZPower_nat identifies every natural power of CZ with diagonal entries omega^(k*j*l), yielding the source statement by choosing g.val.

Scope: All nonzero d and all residues after choosing representatives; stronger than the nonzero-residue paper scope.

Lean: [Relations.lean:157](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:157), [Relations.lean:162](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:162).

Source location: scripts/appendix/sectiontwoproofs.tex:396-399; label lem:multiple-cz.

### Corollary A.13 — match

PDF p. 37. S_pow_dimension states S^d=1 exactly.

Scope: All nonzero natural d in the Lean signature; source odd-prime restriction ensures its S definition matches ordinary half division.

Lean: [Gates.lean:167](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:167).

Source location: scripts/appendix/sectiontwoproofs.tex:415-418; label cor:S-order.

### Corollary A.14 — match

PDF p. 37. CZ_pow_dimension states CZ^d=1 exactly.

Scope: Every nonzero natural d; no quotient or hidden dimension restriction.

Lean: [Gates.lean:192](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:192).

Source location: scripts/appendix/sectiontwoproofs.tex:429-432; label cor:CZ-order.

### Lemma A.15 — match

PDF p. 39. Z_derived_word gives H^2 S H^2 S^(d-1)=Z. Since S^d=1, S^(d-1) is its inverse. This exactly matches the visually checked T3 diagram and the computational-basis Z action.

Scope: Every nonzero odd d. Matrix order is rightmost-first, while the diagram is temporal left-to-right; the transcription reverses it correctly.

Lean: [Gates.lean:466](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:466), [Gates.lean:462](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:462), [Gates.lean:45](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:45).

Source location: scripts/appendix/sectiontwoproofs.tex:549-555; label lem:Z-soundness; diagram T3.

### Lemma A.16 — match

PDF p. 40. X_derived_word gives H S H^2 S^(d-1) H=X, exactly the diagram after temporal-to-matrix-order reversal and the inverse convention.

Scope: Every nonzero odd d; all basis states; diagram visually checked.

Lean: [Gates.lean:471](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:471), [Gates.lean:462](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:462), [Gates.lean:42](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:42).

Source location: scripts/appendix/sectiontwoproofs.tex:575-581; label lem:X-soundness; diagram T2.

### Corollary A.17 — match

PDF p. 42. multiplier_unitary proves that the raw basis permutation for every unit a is unitary. The exact multiplier-word equality identifies the paper's constructed operator with this same permutation.

Scope: The unitarity theorem needs only NeZero d and a unit; source all nonzero a are units because d is prime.

Lean: [Gates.lean:396](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:396), [Gates.lean:101](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:101), [GaussSign.lean:285](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/GaussSign.lean:285).

Source location: scripts/appendix/sectiontwoproofs.tex:759-762; label cor:Mg-unitary.

### Lemma A.18 — match

PDF p. 42. CX_derived proves (I tensor H^3) CZ (I tensor H)=CX. CX is the actual basis permutation (j,l)->(j,l+j); denote_CX_basisMap verifies the fully expanded word on arbitrary wire pairs.

Scope: Nonzero odd d. The source T5 diagram was visually checked, including target-wire H versus H^3 orientation.

Lean: [DerivedGates.lean:94](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/DerivedGates.lean:94), [Relations.lean:184](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:184), [Relations.lean:191](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:191), [ExpandedSoundness.lean:128](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:128).

Source location: scripts/appendix/sectiontwoproofs.tex:780-786; label lem:CNOT-soundness; diagram T5.

### Lemma A.19 — match

PDF p. 43. raw_CX_pow states CX^k = basisMap((j,l)->(j,l+(k mod d)*j)) for every natural k. Taking g.val gives every source nonzero residue.

Scope: Every nonzero d, and every residue is handled. No primality assumption hidden in the result.

Lean: [ExpandedSoundness.lean:68](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:68), [Relations.lean:191](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:191).

Source location: scripts/appendix/sectiontwoproofs.tex:816-819; label lem:multiple-cx.

### Lemma A.20 — match

PDF p. 43. SWAP_derived contains exactly the lambda^2 prefactor visible in the numbered lemma's T4 diagram and concludes the exact raw swap permutation. Expanded SWAP also retains the sign as a scalar word. The earlier unnumbered equation (39) omits this factor and is not the equation Lean proves.

Scope: All nonzero odd d. Match is specifically to the numbered lemma's own diagram, not an endorsement of the inconsistent earlier definition. At d congruent3 mod4 the uncorrected equation(39) denotes -SWAP.

Lean: [DerivedGates.lean:130](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/DerivedGates.lean:130), [ExpandedSoundness.lean:27](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:27), [Relations.lean:127](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:127), [Circuit.lean:118](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:118).

Source location: scripts/appendix/sectiontwoproofs.tex:829-835; label lem:SWAP-soundness; diagram T4 (continues p44).

### Lemma A.21 — match

PDF p. 44. The displayed SWAP;CX;SWAP word has basis map (j,l)->(j+l,l), by composing the inspected exact basis maps. This is a direct elementary instance of denote_append plus basisMap_mul. No separately named XC theorem for T6 is required; the differently defined Figure9.XC is not being substituted for the paper diagram.

Scope: Every nonzero odd d. Lemma heading begins p44, diagram appears p45 (aux label is p45). Earlier SWAP sign inconsistency cancels because this construction has two SWAPs.

Lean: [ExpandedSoundness.lean:115](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:115), [ExpandedSoundness.lean:128](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:128), [Gates.lean:26](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:26), [Circuit.lean:70](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:70).

Source location: scripts/appendix/sectiontwoproofs.tex:861-867; label lem:XC-soundness; diagram T6 p45.

### Lemma A.22 — match

PDF p. 45. denote_CIZ proves the fully expanded SWAP23;CZ12;SWAP23 macro equals the remote CZ13 matrix. The latter diagonal is omega^(j*k), matching the numbered action and diagram.

Scope: All triples of pairwise distinct named wires, all nonzero odd d. The three-wire specialization includes all idle-wire requirements and exact scalars.

Lean: [ExpandedSoundness.lean:137](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:137), [Circuit.lean:123](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:123), [Relations.lean:317](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:317), [Relations.lean:287](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:287).

Source location: scripts/appendix/sectiontwoproofs.tex:876-882; label lem:CIZ-soundness; diagram T7.

### Corollary A.23 — match

PDF p. 45. The numbered diagram is SWAP23;CX12;SWAP23, whose composed exact basis map is (j,l,k)->(j,l,j+k), directly from the general SWAP/CX denotation theorems. This is elementary composition, not a dedicated declaration named CIX. It does not match the erroneous earlier equation (42), which uses I tensor CX in the middle and acts on wires2-3 only.

Scope: All basis labels, nonzero odd d. Match is anchored to the corollary's explicitly displayed defining diagram. Earlier Eq42 is separately recorded as inconsistent source material.

Lean: [ExpandedSoundness.lean:115](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:115), [ExpandedSoundness.lean:128](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:128), [Gates.lean:26](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:26), [Circuit.lean:70](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:70).

Source location: scripts/appendix/sectiontwoproofs.tex:896-902; label cor:CIX-soundness; diagram T8.

### Corollary A.24 — match

PDF p. 45. The numbered diagram swaps wires1-2, applies reverse controlled addition on wires2-3, then swaps1-2 back. Composing the general exact basis maps gives (j,l,k)->(j+k,l,k). This covers the own-diagram claim, not the earlier erroneous equation (43) nor the erroneous last coordinate j in equation (52).

Scope: All basis labels, nonzero odd d. No named XIC wrapper was found; mathematical coverage is by elementary composition of checked general signatures. The reverse controlled addition itself is covered by the same general CX theorem with wire roles interchanged or the A.21 composition.

Lean: [ExpandedSoundness.lean:115](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:115), [ExpandedSoundness.lean:128](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:128), [Gates.lean:26](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:26), [Circuit.lean:70](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:70).

Source location: scripts/appendix/sectiontwoproofs.tex:904-910; label cor:XIC-soundness; diagram T9.

### Lemma A.25 — match

PDF p. 46. All six displayed algebraic equalities are covered: the printed C0 omega^d=1 by omega_pow_dimension; C1 S^d; C2 signed H-square; C3 multiplier powers; C4 with the exact linear Z correction; C5. The source k:Int version of C3 follows from multiplier_mul, inverse laws, and multiplier_unitary; the direct power wrapper is natural-valued. The Figure1 primitive C0 is instead (-omega)^(2d)=1, also proved but not confused with this appendix's C0.

Scope: g is any nonzero field element (Lean unit), not necessarily primitive. Source k:Int versus direct wrapper k:Nat is bridged by the explicitly checked inverse/group laws. No phase correction omitted.

Lean: [RootOfUnity.lean:57](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:57), [Relations.lean:234](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:234), [Relations.lean:237](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:237), [Relations.lean:242](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:242), [Relations.lean:65](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:65), [Relations.lean:260](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:260), [Gates.lean:108](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:108), [Gates.lean:115](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:115).

Source location: scripts/appendix/sectiontwoproofs.tex:922-933; label lem:single-qudit-soundness; C0-C5.

### Lemma A.26 — match

PDF p. 47. All seven displayed matrix identities match: CZ order, SWAP square, CZ/S commutation, CZ/M_g transport with exponent g, SWAP/S, SWAP/H, and the exact CX-to-CZ phase identity. C12 encodes inverse S as phasePower(-1) and inverse CX as CXinv with the explicit inverse identities. Although the source refers back to scalar-defective Eq39 for SWAP, these particular identities are unchanged by SWAP -> -SWAP, so the source inconsistency does not invalidate this lemma.

Scope: All units g; k:Int is vacuous in these formulas. Nonzero odd d suffices for the matrix identities; exact expanded multipliers additionally use source prime d.

Lean: [Relations.lean:246](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:246), [Relations.lean:130](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:130), [Relations.lean:146](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:146), [Relations.lean:168](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:168), [Relations.lean:153](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:153), [Relations.lean:249](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:249), [Relations.lean:214](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:214), [ExpandedSoundness.lean:95](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:95).

Source location: scripts/appendix/sectiontwoproofs.tex:988-1000; label lem:two-qudit-soundness; C6-C12.

### Lemma A.27 — match

PDF p. 48. The swap braid, swap/CZ transport, and CZ/CX interaction agree in exact matrix order and wire positions. C15 uses the remote CZ13 that is proved equal to its SWAP-conjugation definition. The earlier omitted SWAP sign appears an equal number of times on each side, so these identities survive that stale definition as well.

Scope: All nonzero d for raw matrix statements; the expanded normalized words require odd d. The source's g,k hypotheses are unused in the displayed three identities.

Lean: [Relations.lean:292](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:292), [Relations.lean:297](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:297), [Relations.lean:307](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:307), [Relations.lean:317](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:317), [ExpandedSoundness.lean:137](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:137).

Source location: scripts/appendix/sectiontwoproofs.tex:1042-1050; label lem:three-qudit-soundness; C13-C15.

### Proposition A.28 — match

PDF p. 49. figure1_sound states every derivation using the sixteen fully expanded Figure1 schemas (plus sound structural wiring equations) preserves exact complex matrices. This proves the numbered soundness statement with the user-selected -omega Figure1 and raw multipliers. The wider named-wire soundness theorem restricts to adjacent circuits via AdjacentDerives.toDerives; this inference does not rely on the known-false unrestricted completeness target.

Scope: All n and all odd prime d; any unit g suffices for soundness, stronger than the source choice of a multiplicative generator. No multiplier-soundness or Gauss-sign premise in the final theorem.

Lean: [MultiplierSoundness.lean:71](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierSoundness.lean:71), [Circuit.lean:143](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:143), [Circuit.lean:190](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:190), [AdjacentPresentation.lean:30](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentPresentation.lean:30).

Source location: scripts/appendix/sectiontwoproofs.tex:1088-1091; label prop:soundness.

### Lemma B.1 — match

PDF p. 49. All three arbitrary-power Fourier conjugations follow by substituting X/Z exponent coordinates into full-Pauli H conjugation; the reverse formula follows by unitary cancellation.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: corollary.

Lean: [CircuitPauliAction.lean:53](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:53), [CircuitPauliAction.lean:67](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:67), [Gates.lean:64](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:64).

Source location: scripts/appendix/clifford.tex:4.

### Lemma B.2 — match

PDF p. 49. The seven H^2/H^3 actions are direct finite compositions of the formal full-Pauli H action. No quotient or extra phase is substituted.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: corollary.

Lean: [CircuitPauliAction.lean:53](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:53), [CircuitPauliAction.lean:168](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:168), [CircuitPauliAction.lean:200](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:200).

Source location: scripts/appendix/clifford.tex:22.

### Lemma B.3 — match

PDF p. 50. Both controlled-addition orientations and their six Pauli-action instances follow from exact word conjugation with expanded H-CZ-H^3 macros and corresponding coordinate substitution.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: corollary.

Lean: [CircuitPauliAction.lean:200](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:200), [Circuit.lean:115](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Circuit.lean:115), [ExpandedSoundness.lean:128](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/ExpandedSoundness.lean:128), [Figure9Syntax.lean:85](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Figure9Syntax.lean:85).

Source location: scripts/appendix/clifford.tex:37.

### Lemma B.4 — match

PDF p. 51. Arbitrary X^a/Z^a conjugation is obtained directly by specializing the full-Pauli S formula; its phase is quadratic(a)=a(a-1)/2. The reverse action follows by unitary cancellation.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: corollary.

Lean: [CircuitPauliAction.lean:57](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:57), [CircuitPauliAction.lean:92](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitPauliAction.lean:92).

Source location: scripts/appendix/clifford.tex:60.

### Lemma B.5 — match

PDF p. 51. The arbitrary S-power conjugations follow entrywise from phasePower_nat, the diagonal multiplication formulas, and quadratic_add with shift a=1; q(1)=0 gives the stated phase-free pushing formula. Replacing the phase parameter by its negative gives inverse conjugation. Diagonal commutation gives preservation of Z. No dedicated closed-form wrapper was located or added; the explicit bridge is documented in foundations.md.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: reviewed elementary corollary; wrapper absent.

Lean: [Relations.lean:51](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:51), [Relations.lean:56](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:56), [Relations.lean:60](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:60), [Relations.lean:207](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:207), [MultiplierDerivation.lean:54](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierDerivation.lean:54), [MultiplierDerivation.lean:58](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierDerivation.lean:58), [Gates.lean:287](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:287).

Source location: scripts/appendix/clifford.tex:90.

### Lemma B.6 — match

PDF p. 52. The general exact identity Q(b)T(a)=phase(b*q(a)) • (T(a)D(a*b)Q(b)) follows entrywise from q(j+a)=q(j)+q(a)+j*a. Multiplication by Q(-b) gives the displayed conjugation, and b -> -b gives its inverse. This checks the central quadratic phase, not just the symplectic exponents. No dedicated closed-form wrapper was located or compiled; foundations.md records the elementary bridge.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: reviewed elementary corollary; wrapper absent.

Lean: [Relations.lean:51](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:51), [Relations.lean:56](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:56), [Relations.lean:60](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:60), [Relations.lean:207](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:207), [MultiplierDerivation.lean:54](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierDerivation.lean:54), [MultiplierDerivation.lean:58](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierDerivation.lean:58), [Gates.lean:287](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:287).

Source location: scripts/appendix/clifford.tex:119.

### Lemma B.7 — match

PDF p. 52. By B.5, X Z^(-a)=S^(-a) X S^a. Conjugation preserves natural powers, so its b-th power equals S^(-a) X^b S^a; the B.6 identity gives phase(-a*q(b)) • X^b Z^(-a*b), with q(b)=b(b-1)/2. Thus the formula is an elementary consequence of the existing diagonal and quadratic identities. The wrapper and this assembled bridge were not compiled during the audit.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: reviewed elementary corollary; wrapper absent.

Lean: [Relations.lean:51](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:51), [Relations.lean:56](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:56), [Relations.lean:60](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:60), [Relations.lean:207](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:207), [MultiplierDerivation.lean:54](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierDerivation.lean:54), [MultiplierDerivation.lean:58](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/MultiplierDerivation.lean:58), [Gates.lean:287](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:287).

Source location: scripts/appendix/clifford.tex:153.

### Lemma B.8 — match

PDF p. 53. Both (-omega)^d=-1 and (-omega)^(d+1)=omega are explicit scalar-generator theorems.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: direct.

Lean: [RootOfUnity.lean:77](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:77), [RootOfUnity.lean:80](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/RootOfUnity.lean:80).

Source location: scripts/appendix/clifford.tex:178.

### Lemma B.9 — match

PDF p. 53. Exact X implementation matches after reversing temporal word order; proof keeps actual phases.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: direct.

Lean: [Gates.lean:471](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:471), [CircuitSemantics.lean:195](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/CircuitSemantics.lean:195).

Source location: scripts/appendix/clifford.tex:194.

### Lemma B.10 — match

PDF p. 53. S-prime=H^2 S H^2 and the exact Z word give the stated identity.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: direct.

Lean: [Gates.lean:455](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:455), [Gates.lean:466](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Gates.lean:466).

Source location: scripts/appendix/clifford.tex:212.

### Lemma B.11 — corrected statement

PDF p. 54. Printed SWAP diagram omits lambda^2. Lean proves the phase-corrected exact identity; the raw threefold CZ-(H tensor H) word differs by a sign for d=3. Projectively the printed diagram remains valid, but it is not the literal exact equality.

Scope: Odd prime d; arbitrary finite arity where relevant; matrix order reverses temporal diagram order.

Evidence type: direct.

Lean: [DerivedGates.lean:113](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/DerivedGates.lean:113), [DerivedGates.lean:130](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/DerivedGates.lean:130).

Source location: scripts/appendix/clifford.tex:232.

### Proposition D.1 — missing

PDF p. 56. No theorem implementing generic subsystem preservation implies Clifford tensor factorization was located. The nearest result lift_restrict factors a symplectic map fixing the last X/Z vectors as a lifted lower-arity symplectic map. That has different hypotheses, only a one-wire distinguished subsystem, and an exponent-map conclusion; it is not C=C1 tensor C2 up to scalar for arbitrary k1,k2.

Scope: Repository-wide searches for tensor/kronecker/untangled/factorization/subsystem and nearby normalizer modules found concrete tensor-placement laws and this special symplectic restriction only. D.1 is unnecessary for the alternate explicit rewrite proofs but remains a missing paper statement.

Lean: [NormalInduction.lean:319](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/NormalInduction.lean:319), [Relations.lean:100](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/Relations.lean:100).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:15.

### Lemma D.2 — match

PDF p. 58. All nonzero (a,b) branches give H:A_(a,b)->A_(b,-a) and S:A_(a,b)->A_(a,b-a), with the residual on the same wire. Lean gives explicit S-power residuals (or empty residual); labels and allowed support agree.

Scope: The existential wrappers hide updated labels, but branch definitions/signatures explicitly give the source labels. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [SymplecticOneWire.lean:280](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticOneWire.lean:280), [SymplecticOneWire.lean:339](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticOneWire.lean:339), [SymplecticOneWire.lean:354](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticOneWire.lean:354), [AdjacentBoxCases.lean:29](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:29), [AdjacentBoxCases.lean:38](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:38), [AdjacentBoxCases.lean:57](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:57), [AdjacentBoxCases.lean:67](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:67), [AdjacentBoxCases.lean:77](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:77).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:32.

### Lemma D.3 — match

PDF p. 58. Both branches: a=0 leaves A_(0,b) and a two-wire residual; a≠0 gives A_(0,-a) on the lower wire, B_(a,b), and a two-wire residual. Formal expansion reads in reverse list order relative to the printed temporal diagram.

Scope: ABox.nonzero supplies b≠0 in the a=0 branch. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:100](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:100), [AdjacentBoxCases.lean:107](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:107), [SymplecticTwoWireA.lean:274](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticTwoWireA.lean:274).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:64.

### Lemma D.4 — match

PDF p. 59. All cases of CZ through A then B are covered: a=0,c=b collision moves to A_(b,d); a=0,c≠b gives A_(0,b-c),B_(c,d); a≠0 gives A_(a,b-c),B_(c,d-a). The first two residuals can use two wires; the last residual is only on the lower wire. Lean splits c=0 additionally, preserving all cases.

Scope: The paper uses d simultaneously for field size and a B label; Lean renames the latter k. No nonzero condition on that label. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:238](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:238), [AdjacentBoxCases.lean:247](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:247), [AdjacentBoxCases.lean:257](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:257), [AdjacentBoxCases.lean:266](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:266), [AdjacentBoxCases.lean:274](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:274), [SymplecticTwoWireAB.lean:161](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticTwoWireAB.lean:161), [SymplecticTwoWireAB.lean:231](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticTwoWireAB.lean:231).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:82.

### Lemma D.5 — match

PDF p. 60. All four a/b zero cases implement H on the upper input, update B_(a,b) to B_(b,-a), and leave a residual only on the lower output. The nonzero/nonzero branch explicitly uses a multiplier and S on that output; it is not an arbitrary two-wire residual.

Scope: Both labels range over all residues; zero cases inspected separately. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:115](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:115), [AdjacentBoxCases.lean:122](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:122), [AdjacentBoxCases.lean:128](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:128), [AdjacentBoxCases.lean:135](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:135).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:131.

### Lemma D.6 — match

PDF p. 60. S on the upper input updates B_(a,b) to B_(a,b-a); a=0 leaves a lower S residual and a≠0 has empty residual. Both formal branches are exact derivations, stronger than the contextual symplectic requirement.

Scope: Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:143](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:143), [AdjacentBoxCases.lean:149](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:149).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:178.

### Lemma D.7 — match

PDF p. 61. S on the lower input leaves B labels unchanged and yields an explicitly expanded two-wire residual. The residual has the source-allowed C2 support for every label.

Scope: No requirement that this residual be single-wire was imposed or inferred. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:155](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:155), [AdjacentBoxCases.lean:162](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:162), [AdjacentBoxCases.lean:170](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:170).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:224.

### Lemma D.8 — match

PDF p. 61. All four zero/nonzero cases implement lower H, update D_(a,b) to D_(b,-a), and yield a residual only on the upper output.

Scope: B/H and D/H branches are distinct and the wire orientation was checked in the rendered diagrams. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:178](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:178), [AdjacentBoxCases.lean:185](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:185), [AdjacentBoxCases.lean:191](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:191), [AdjacentBoxCases.lean:198](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:198).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:242.

### Lemma D.9 — match

PDF p. 62. Lower S updates D_(a,b) to D_(a,b-a), with upper S residual if a=0 and empty residual if a≠0. Both branches are exact. 

Scope: Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:206](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:206), [AdjacentBoxCases.lean:212](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:212).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:290.

### Lemma D.10 — match

PDF p. 63. Upper S commutes through D to a lower S, leaving D unchanged and taking the arbitrary upper dir to the identity. Formal result is exact for all labels.

Scope: Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:218](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:218), [SymplecticTwoWireD.lean:113](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/SymplecticTwoWireD.lean:113).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:338.

### Lemma D.11 — match

PDF p. 64. CZ updates D_(a,b) to D_(a,b-1), leaves S^a on the lower output, and an explicit H S^(-1/a) H^-1 upper residual when a≠0. a=0 has no residual. This matches the source division of supports and lower S exponent. 

Scope: Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentBoxCases.lean:224](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:224), [AdjacentBoxCases.lean:230](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentBoxCases.lean:230).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:385.

### Lemma D.12 — match

PDF p. 64. CZ through the two B boxes updates lower B_(a,b) to B_(a,b-c) and upper B_(c,d) to B_(c,d-a), with residual only on the two lower wires. All four zero/nonzero branches exist. Lean lists upper box first in matrix order; swapping the label names aligns the equations.

Scope: Printed sentence only binds a,b, while c,d appear in its diagram; Lean explicitly universally quantifies all four. This is an editorial omission in the printed binder, not a restriction to special c,d. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentThreeWireBoxCases.lean:99](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:99), [AdjacentThreeWireBoxCases.lean:109](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:109), [AdjacentThreeWireBoxCases.lean:122](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:122), [AdjacentThreeWireBoxCases.lean:135](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:135).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:433.

### Lemma D.13 — match

PDF p. 65. A CZ on the lower two wires passes B on the upper two without changing its labels, leaving a three-wire residual. Both branches are exact; the residual contains the expanded remote CZ and a lower CZ power.

Scope: Allowed dir is C3, so the remote interaction inside the explicit residual is permitted. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentThreeWireBoxCases.lean:40](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:40), [AdjacentThreeWireBoxCases.lean:48](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:48).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:482.

### Lemma D.14 — match

PDF p. 66. CZ through the D ladder updates upper D_(a,b) to D_(a,b-c) and lower D_(c,d) to D_(c,d-a), with a residual only on the upper two wires. All four zero/nonzero branches have the expected supports.

Scope: Printed binder again names only a,b while the diagram contains c,d; Lean explicitly binds four labels. Formal variable renaming reverses upper/lower label names but not wire order. Interpreted as symplectic box relations in the paper Section 4.1 context (scripts/4-completeness.tex:15,35). Some branches are exact AdjacentDerives, others only AdjacentSymplecticDerives. Thus this row does not certify a global-phase-only or exact-unitary reading of the unadorned diagram symbol. Lean assumes odd prime d and a unit g with orderOf g=d-1 for the rewrite derivations; such g exists for these dimensions. Canonical Fin 2/Fin 3 is precisely local two/three-qudit arity, not a dimension specialization.

Lean: [AdjacentThreeWireBoxCases.lean:56](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:56), [AdjacentThreeWireBoxCases.lean:64](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:64), [AdjacentThreeWireBoxCases.lean:73](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:73), [AdjacentThreeWireBoxCases.lean:82](/Users/sarahli/Desktop/PhD-Projects/GitRepo/QuditCliffordLean/QuditClifford/AdjacentThreeWireBoxCases.lean:82).

Source location: /Users/sarahli/Desktop/PhD-Projects/papers/QupitCliffGenrel-paper/scripts/appendix/push-normal.tex:501.
