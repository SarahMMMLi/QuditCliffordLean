# Source map for the remaining rewrite-completeness proof

This is a source audit and port plan, not a Lean completeness theorem. The
current Lean matrix normal form and generated-group results do not prove that
equal circuits are related by the paper's rewrite rules.

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

## Lowest-friction Lean route

1. Add a literal Figure 9 relation and a separate auxiliary symplectic
   relation. Reuse `Presentation.Derives` with explicit relabeling and
   disjoint-wire commutation. A list representation removes the Agda tree
   associativity bookkeeping. For long group-algebra chains, work in the
   quotient by this **syntactically generated** congruence and recover a
   derivation from quotient equality, as `PresentedCircuit.lean` already
   does with `classWord_eq_iff_derives`. This permits Lean's group and power
   lemmas without replacing rewriting by matrix equality. Keep the Figure 1
   exact relation distinct.
2. Prove the small bridge from Figure 9 to the auxiliary relation first.
   Use the pinned `Paper-V0`/`Paper-V1` comparison chains as a guide, checking
   C13/C14 and the multiplier inversion explicitly. This is the source
   correspondence obligation most likely to be missed by a mechanical port.
3. Port the one-wire A/E chains, then the two-wire D chains; obtain B chains
   through the source's explicit duality. Port CZ-through-A/AB and the
   three-wire DD, BB, and B cases. Each result must have type
   `Presentation.Derives R lhs rhs` for concrete words.
4. Prove that each primitive gate can be pushed through the current literal
   recursive normal-form word, using these local derivations. The existing
   `SymplecticNormalForm` uniqueness theorem and `NormalCircuit` action theorem
   can discharge semantic uniqueness after a **syntactic** reduction theorem
   has been proved. There is no need to port Agda's generic coset tower if a
   direct induction on the existing Lean grammar suffices.
5. Apply `Presentation.complete_of_normal_forms`. Only then label the result
   symplectic rewrite completeness. Next derive the required Pauli-corrected
   Figure 9 equations from the exact Figure 1 relation and discharge Pauli
   normalization. `ProjectiveRewrites.lean` now supplies the final exact
   scalar lift: `figure1Complete_of_projectiveComplete` takes the still-open
   `Figure1ProjectiveComplete` as its input. The generated matrix-group
   classification cannot replace that missing syntactic derivation theorem.

No Lean axioms, placeholder proofs, or semantic-equality rewrite constructors
are introduced by this audit document.

For the main exact Figure 1 theorem alone, a second possible route is to port
the release's `Paper-V1/Presentation.agda` projective result directly: its 15
nonscalar axiom families closely match the current Lean C1–C15. Then use the
proved concrete scalar-lifting theorem. This route still requires translating
the S/multiplier conventions and proving the syntactic presentation maps. It
would establish the main theorem without automatically discharging the
separate, literal Figure 9 statement of Theorem 4.4.
