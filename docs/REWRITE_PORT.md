# Source map for the remaining rewrite-completeness proof

This is a source audit and port plan, not a Lean completeness theorem. The
matrix normal form and generated-group results alone do not prove that equal
circuits are related by the paper's rewrite rules. The one-qudit completeness
specialization is now independently proved by syntactic normalization in Lean.

## Current Lean port

`SymplecticRewrites.lean` defines an explicit erasure of the actual Figure 1
rules, adding only scalar/X/Z deletion. This is not the literal eighteen-rule
Figure 9 relation. `PresentedPauliNormality.lean`, `PauliWordRewrites.lean`,
`SymplecticKernel.lean`, and `PauliLifting.lean` prove its exact signed-Pauli
kernel and lift every derivation with a unique correction. Consequently
`figure1Complete_iff_symplecticErasureComplete` identifies the helper exact
and erased completeness properties. Both unrestricted properties are false
at three qutrits, as proved below. The source-restricted target and its
proof-transport obligation are distinct.

The following local cases have been ported to actual exact or erased Figure 1
derivations, using the literal Figure 6 words and selected raw multipliers:

| Box family | Lean module | Checked cases |
| --- | --- | ---: |
| One-wire A/E | `SymplecticOneWire.lean` | 6 of 6 |
| Two-wire A/CZ | `SymplecticTwoWireA.lean` | 2 of 2 |
| Two-wire B/H/S | `SymplecticTwoWireB.lean` | 9 of 9 |
| Two-wire D/H/S/CZ | `SymplecticTwoWireD.lean`, `SymplecticTwoWireDCZ.lean` | 9 of 9 |
| Three-wire B/CZ | `SymplecticThreeWireB.lean` | 2 of 2 |
| Two-wire AB/CZ | `SymplecticTwoWireAB.lean`, `SymplecticTwoWireABNonzero.lean` | 6 of 6 |
| Three-wire DD/CZ | `SymplecticThreeWireDD.lean`, `SymplecticThreeWireDDNonzero.lean` | 4 of 4 |
| Three-wire BB/CZ | `SymplecticThreeWireBB.lean` | 4 of 4 |

All 42 printed case branches are now checked in the named-wire helper
presentation. Their derivation from the separate literal Figure 9 presentation
is still open; this table does not assert Theorem 4.4. It also does not by itself
show that every helper proof can be replayed in the restricted adjacent
presentation described below. `MultiplierRewrites.lean` and `MultiplierControlledZRewrites.lean` derive
the all-unit multiplier laws from finite C3 and primitive-generator C4/C9.
`ThreeWireControlledRewrites.lean` and `ThreeWirePhaseTransport.lean` derive
the exact adjacent/remote-CZ commutations and reverse C15.
`SymplecticThreeWireB.lean` extends C15 to all powers and proves both B/CZ
cases exactly. `BoxDuality.lean` proves exact B/D and BB/DD Fourier duality,
providing syntactic transport between the remaining three-wire families.

`OneQuditCompleteness.lean` uses the six A/E cases in an actual induction on
primitive words. Concrete E-A label uniqueness and exact lifting then give
`figure1Complete_one`, including `-ω`, for all odd primes and primitive roots.
`RelabelRewrites.lean` proves arbitrary injective wire transport of every
schema and derivation, and `WireContextRewrites.lean` proves interchange of
embedded words with disjoint supports. `NormalIdentity.lean` derives the exact recursive
identity normal word at every arity, with the Figure 6-compatible E(0) seed.
`XNormalPhaseRewrites.lean` proves phase absorption through every D/E layer by
an actual recursive exact derivation. `NormalRewriteInduction.lean` supplies
word induction from a stated gate-closure hypothesis in the helper relation;
it does not prove that hypothesis. The remaining normalization task must use
the paper’s adjacent primitive alphabet and source-restricted rewrite relation.

## Adjacent source syntax versus the named-wire helper syntax

The paper’s Definition 4.1 specifies adjacent dirty CZ gates (printed pp. 22–23;
`scripts/4-completeness.tex`, lines 40–48). Figure 4 T7 on printed p. 15 defines
a CZ across an idle wire by a SWAP–CZ–SWAP word. The pinned
`Circuit/Base.agda` lines 47–54 has only arity-one/arity-two gates and shifts;
`Symplectic/Syntactics/Gates.agda` lines 59–62 declares CZ at arity two, and
lines 193–197 defines `CZ02` by the SWAP expansion. It has no independent
nonadjacent primitive CZ.

The original Lean named-wire helper alphabet did have such extra letters.
Its two structural equations do not automatically equate them with routed
macros. The attempted identification is formally refuted below; it cannot be
inferred from equal matrices. `AdjacentCircuit.lean` now defines
the canonical adjacent alphabet explicitly. `AdjacentPresentation.lean`
restricts **both sides of each rule**, and takes its own contextual closure;
it proves adjacency is preserved throughout derivations. Restricting only the
inputs while allowing arbitrary named-wire intermediate derivations would be
a weaker result and is deliberately not used as the main target.

`Circuit.MainTheorem` now refers to this source-restricted relation. The former
unrestricted proposition is named `NamedWireMainTheorem`. Zero- and one-qudit
completeness transfer because all words at those arities are adjacent.
The 42 helper derivations, recursive sweeps, and Pauli lifting remain valid
as stated, but their transport to the restricted relation must be supplied
before using them to prove the paper’s multiwire completeness theorem.
No coherence equation or semantic-equality rule has been added to conceal
this distinction.

The obstruction is now **proved in Lean**, not only suspected:
`NamedWireCountermodel.lean` interprets the named-wire gates as finite matrices
over `ZMod 3`, reversing every primitive CZ coupling. Kernel-checked finite
calculations verify all sixteen schema families and all structural cases.
The derived remote coupling differs from the independent direct CZ coupling.
`not_figure1Complete` and `not_namedWireMainTheorem_three` therefore refute the
old unrestricted target at three qutrits. The actual adjacent source excludes
the independent remote letter and is not refuted by this model: on a line,
the reversed adjacent couplings can be obtained by alternating local sign
changes, while adding the independent third edge creates the discrepancy.

`AdjacentWireRewrites.lean` starts restricted replay with exact C7/C10/C11
transport, including opposite-wire H/S transport without reverse-CZ aliases.
`AdjacentOneWireRewrites.lean` replays any exact one-wire proof on a chosen wire.
`AdjacentNormalCircuit.lean` and `AdjacentExactNormal.lean` prove the entire
normal syntax remains adjacent. `AdjacentNormalization.lean` identifies the
remaining source theorem precisely with restricted exact normalization.


## Pinned external source

The attached paper's bibliography entry `qupitgit` ([7]) points to the
[v1.0-quantum-submission release](https://github.com/onestruggler/acir/releases/tag/v1.0-quantum-submission).
The audited tag resolves to commit
`db998e640dad8dbb0732a51ae599f0c34f69c7ac`. All links below are pinned to that
commit. The source was inspected on 2026-09-22. Its README specifies Agda 2.8
and standard library 2.4.

The relevant entry point is
[MainTheorems.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/MainTheorems.agda).
It states symplectic normal-form uniqueness, a simplified symplectic
presentation, and two presentations of the **projective** Clifford group
`Pauli n ⋊ Sp(2n, ℤ/pℤ)`. The projective result does not establish the user's
chosen exact scalar convention `−ω`.

The separate
[Clifford/Qupit/Presentation.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/Clifford/Qupit/Presentation.agda)
develops an exact presentation of an abstract cocycle central extension, with
scalar `ω` and relation `ω^p=1`. It lies outside this `MainTheorems` import
closure and uses a different scalar convention. Its `split`/`corr-witness`
argument is useful reference material for lifting a projective derivation;
its theorem cannot be substituted for exact matrix Figure 1 completeness
under `−ω` of order `2d`.

Static inspection of the 176 repository-local modules in this entry point's
import closure found `--safe` on every module and no active `postulate`, hole,
standalone question-mark metavariable, or `primTrustMe`. There are unfinished
experiments inside block comments; a raw text search for holes also finds
those. Some status comments are stale, notably claims that surjectivity is
still postulated: the actual `PresentationFull` theorem imports the proved
`surj-nf`.

The first local validation used Agda 2.8.0 and the installed standard library
**2.3**, whereas the release requests **2.4**:

* `agda Examples/Groups/Symplectic/Lemmas/BoxRelations.agda`: exit 0.
* `agda Examples/Groups/Symplectic/BR/Two/L2-CZ.agda`: exit 0.
* `agda MainTheorems.agda`: exit 42 at `Normalization.agda:431`, where the
  installed `Homomorphic₂` API expects explicit carrier types. The check
  reached and checked the box-relation modules before this error. This is a
  library-version compatibility failure; it is not evidence of a missing
  box derivation. No external source was patched to obtain these results.

The follow-up check pinned
[Agda standard library v2.4](https://github.com/agda/agda-stdlib/tree/2a5a0dec0a3cb5c87468ce101388a513d39dbf10)
at commit `2a5a0dec0a3cb5c87468ce101388a513d39dbf10`, using a separate temporary
checkout and explicit include paths, with no changes to the installed
libraries or the proof source. A small compatibility probe confirms that the
same `Homomorphic₂` application succeeds against 2.4. The full command is:

```sh
agda --no-libraries -i . -i /path/to/agda-stdlib-2.4/src \
  -WnoUnsupportedIndexedMatch MainTheorems.agda
```

**The full follow-up check passed with exit 0 on 2026-09-22.** The output
contained 462 module-checking lines and no errors. `git status --short` and
`git diff --exit-code` confirmed that the audited release source was unchanged.
Thus both the box derivations and the full `MainTheorems.agda` symplectic and
projective presentation chain were independently revalidated with the declared
dependencies. This external Agda validation is not a Lean proof of those
theorems and does not establish the different exact `−ω` presentation.

## Where the syntactic proofs live

* [Presentation/Base.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Presentation/Base.agda)
  defines the inductive congruence `_≈_`: reflexivity, symmetry, transitivity,
  concatenation congruence, associativity, units, and an explicit generating
  relation constructor. Equality of interpretations is **not** a constructor.
* [Circuit/Base.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Circuit/Base.agda)
  supplies wire shifting and disjoint-support structural commutation.
* [Symplectic/Syntactics/Gates.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/Symplectic/Syntactics/Gates.agda)
  defines a 17-family older symplectic presentation, together with derived
  words. [Simplified/Syntactics.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/Symplectic/Simplified/Syntactics.agda)
  instead has 15 group-specific axiom families, using one primitive-root
  multiplier. [Simplified/Iso.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/Symplectic/Simplified/Iso.agda)
  gives explicit `f-well-defined` and `g-well-defined` maps between these
  generating relations; its imports `Lemmas.agda` and `LemmasCZ.agda` contain
  their derivations.
* [Lemmas/BoxRelations.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/Symplectic/Lemmas/BoxRelations.agda)
  is a convenient summary of most box-pushing theorems. Its proofs refer to
  explicit equational chains in `BR/One`, `BR/Two`, and `BR/Three`.
  **The CZ-through-A/AB family is not exported by this summary**; use
  `BR/Two/L2-CZ.agda` as well.
* [Normalization.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/Symplectic/Normalization.agda)
  supplies `nfp'-sec` and `nfp'-sec-agree`, with a syntactic retraction. The
  normalizer uses a width-indexed Reidemeister–Schreier tower and the
  `Normalization/Pushing` modules. It is more explicit than the paper's
  Lemma 4.2 termination argument, which refers to the analogous qubit proof.

## The 42 Appendix F cases

The counts below are the actual numbers of `equiv_s` rows in the seven TeX
figures included by `scripts/appendix/boxrelations.tex`; they sum to 42.
`BR/` below abbreviates `Examples/Groups/Symplectic/BR/` in the pinned release.
These are derivations for the source's concrete A/B/D/E words, with exhaustive
zero/nonzero branches, not just evaluations of their matrices.

| Attached-paper source | Cases | Source proof entry points |
| --- | ---: | --- |
| `figures/BoxRelations/br1.tikz`: H through A (3), S through A (2), S through E (1) | 6 | `BR/One/A.agda`: `fig-24-1/2/3`, `fig-25-1/2`, `lemma-single-qupit-br-A`; `BR/One/E.agda`: `lemma-single-qupit-br-E` |
| `br2CZL.tikz`: CZ through A or AB | 8 | `BR/Two/A-CZ.agda`: `lemma-A-CZ-1/2`; `BR/Two/L2-CZ/{Left,Right}.agda`: `lemma₁`, `lemma₂`; combined `L2-CZ.agda`: `lemma-dir-and-l'` |
| `br2HuSuSdB.tikz`: upper H/S and lower S through B | 9 | `BR/Two/B.agda`: `dir-of`, `b'-of`, `lemma-B-br` |
| `br2HdSuSdCZD.tikz`: lower H/S, upper S, CZ through D | 9 | `BR/Two/D.agda`: `dir-of`, `d'-of`, `lemma-D-br` |
| `br3CZuBB.tikz`: upper CZ through two B boxes | 4 | `BR/Three/BB-CZ.agda`: `dir-of`, `vb'-of`, `lemma-dir-and-vb'`; uses the explicit B/D duality |
| `br3CZdBu.tikz`: lower CZ through upper B | 2 | `BR/Three/B-CZ.agda`: `dir-of`, `lemma-dir-and-b'-cz` |
| `br3CZdDD.tikz`: lower CZ through two D boxes | 4 | `BR/Three/DD-CZ.agda`: `dir-of`, `vd'-of`, `lemma-dir-and-vd'` |

The reachable `BR` modules total about 7,000 source lines. This is a substantial
proof port; the family summary by itself omits the auxiliary swap, conjugation,
field-arithmetic, and wire-embedding lemmas.

## Figure 9 is not the 15-constructor `Simplified` relation

The attached PDF's Figure 9 has the following literal diagram inventory.
The last column gives a useful source location, **not** a claim that a
constructor there is the identical equation with identical definitions.
`Paper-V0` and `Paper-V1` below abbreviate the corresponding directories under
`Examples/Groups/ProjectiveClifford/Qupit/`.

| Figure 9 | Diagram content | Closest source entry |
| --- | --- | --- |
| C1 | `S^d = id` | `order-S` |
| C2 | `H² = M₋₁` | `order-H` |
| C3 | `M_g^k = M_(g^k)` | `M-power` |
| C4 | S/multiplier commutation with exponent `g⁻²` | `semi-MR`; erase its Pauli correction and translate multiplier convention |
| C5 | `H² S H² S = S H² S H²` | `comm-HHSHHS` |
| C6 | `CZ^d = id` | `order-CZ` |
| C7 | `SWAP² = id` | `order-Ex` |
| C8 | upper S commutes with CZ | `comm-CZ-S↑` |
| C9 | multiplier through CZ with exponent `g⁻¹` | `semi-M↑CZ`, after exponent conversion |
| C10 | S transported through SWAP | `semi-Ex-S↑` |
| C11 | H transported through SWAP | `semi-Ex-H↑` |
| C12 | CZ commutes with SWAP | `Paper-V0/Lemmas.agda`, `Ex-Conjugation.lemma-Ex-CZ` |
| C13 | S through reverse-direction CX, with S/CZ corrections | `blake-c12`, after wire/order rearrangement |
| C14 | CZ through reverse-direction CX, producing `S⁻²` | `Symplectic/Lemmas/Ex-Sym3.agda`: `lemma-semi-CXCZ^k` at `k=1`, with the wires exchanged |
| C15 | two overlapping adjacent CZ gates commute | `selinger-c12`; `Paper-V0/Lemmas.agda`, `Three-Wire.lemma-selinger-c12` |
| C16 | braid relation for adjacent SWAPs | `yang-baxter` |
| C17 | CZ transported through two SWAPs | `cz-slide` |
| C18 | overlapping CX/CZ commute with an extra nonadjacent CZ | `semi-CX↑-CZ↓` |

In particular, `Symplectic/Simplified/Syntactics.agda` has Selinger-style
`selinger-c10` through `selinger-c15` axioms in place of this literal SWAP
presentation. The release contains a route through
[Paper-V0/Iso.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/ProjectiveClifford/Qupit/Paper-V0/Iso.agda)
and its roughly 4,700-line `Lemmas.agda`, plus
[Paper-V1/Iso.agda](https://github.com/onestruggler/acir/blob/db998e640dad8dbb0732a51ae599f0c34f69c7ac/Examples/Groups/ProjectiveClifford/Qupit/Paper-V1/Iso.agda).
The latter relates S-based and centered-phase-based multiplier definitions.
The release's `MainTheorems` does not directly state a theorem whose input is
a relation with exactly the 18 printed Figure 9 constructors. Porting the
15-family theorem and renaming it “Theorem 4.4” would leave an unproved
presentation-comparison step.

## Convention checks required before translation

1. **Order and wires.** Agda's `_•_` is matrix-factor order. A paper diagram
   is read temporally left to right. Current Lean `Circuit.Word` also uses
   matrix-factor order, so preserve Agda factor order when flattening trees
   into lists. Agda's unshifted gate acts on the bottom wire; `_↑` shifts
   upward. Write down the finite-wire relabeling explicitly. Agda's
   `ProjectivePauli/Semantics.agda` uses pairs `(x,z)`, with `pZ=(0,1)` and
   `pX=(1,0)`; Lean `NormalBoxes.Vector` uses `(z,x)`. Swapping components
   identifies their alternating forms without an additional sign.
2. **Multiplier inversion.** In symplectic Agda, the historical `M` is `ZM`,
   while Figure 6's A boxes use `XM`; `XM x = ZM (x⁻¹)` is proved as
   `XM≡ZM⁻¹`. Current Lean's physical multiplier agrees with the paper's
   X-scaling convention. Do not translate every Agda `M x` as the current
   Lean `multiplier x`. The `g`-primitive-root witness is an explicit module
   parameter in the simplified source presentation.
3. **Scalars.** Agda's `Ex` and multipliers in the symplectic development are
   scalar-free words. Current `NormalCircuit` preserves the exact `−ω`
   corrections in physical multiplier and SWAP words. For Theorem 4.4, use a
   separate explicit scalar-erasure translation, then lift by proved Pauli
   and scalar corrections. Never infer an exact rewrite from equality of
   exponent actions.
4. **Equation (12) in the attached PDF is inconsistent with Figure 6.** It
   prints `id = A₀₁ ; E_(d−1)`. Figure 6 gives `A₀₁ = M₁ = id` and
   `E_(d−1) = S`, so this is not even a symplectic identity for odd prime d.
   The Figure 6-compatible identity uses `E₀`. The two-wire `B₀₀ ; D₀₀`
   identity is consistent. Use the verified box definitions and record this
   correction when proving the normal identity seed.
5. **Other attached-source discrepancies remain relevant.** Appendix C's
   printed A₀b action and one B₀b action disagree with Figure 6. The current
   Lean boxes and the release's `Normalization/Section.agda` use the concrete
   Figure 6 definitions. Do not use the stale tables to change those words.

## Remaining Lean route after the alphabet correction

1. Replay the checked local helper derivations in the canonical adjacent
   presentation. Use `AdjacentDerives` or its explicitly defined scalar/Pauli
   erasure, including restricted group and cancellation infrastructure.
   `AdjacentWireRewrites` and `AdjacentOneWireRewrites` begin this replay.
   Adjacent endpoints alone do not certify that a helper proof stays adjacent.
2. Prove the recursive Z/X sweeps on `AdjacentWord` and `ZSweepWord`, then
   normalization under every adjacent primitive generator. The 42 helper
   branches supply the algebraic chains; their restricted derivations must
   still be checked. `NormalSweepSyntax` supplies the dirty grammar and its
   first-wire invariant, not the normalization theorem.
3. Transport the proved Pauli/scalar lifting to the restricted relation.
   `Circuit.adjacentFigure1Complete_iff_derivablyNormalizes`
   in `AdjacentNormalization.lean` records the exact remaining reduction target.
   All concrete exact normal words are already proved adjacent. Neither
   semantic uniqueness nor cardinality replaces syntactic reduction.
4. Separately define the literal eighteen-rule Figure 9 presentation and
   prove its correspondence with the restricted auxiliary relation and all
   42 box cases. Preserve its multiplier convention and the selected exact
   scalar distinction. Only then claim the separate Theorem 4.4 statement.

A possible alternative for the exact theorem is to port the release's
`Paper-V1/Presentation.agda` projective result directly on its adjacent
alphabet, then replay the scalar lifting in that same alphabet. Its 15
nonscalar schemas are close to the printed C1–C15, but both convention
translation and syntactic presentation maps still require proofs. This
would not automatically establish the separate Figure 9 theorem.

The former unrestricted `Figure1ProjectiveComplete` is **not** a remaining
target to prove: its equivalence with the refuted named-wire exact target
rules out that route. No new coherence axiom or semantic-equality rewrite
constructor is introduced to repair the mismatch.
