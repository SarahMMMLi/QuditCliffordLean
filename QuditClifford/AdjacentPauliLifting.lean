import QuditClifford.AdjacentPauliWordRewrites
import QuditClifford.AdjacentPauliKernel
import QuditClifford.GeneratedScalarKernel

/-!
# Exact lifting of guarded Pauli-erased derivations

The kernel of restricted Pauli erasure is the concrete adjacent Pauli
subgroup, whose signed coordinates have already been proved faithful.
Hence a guarded erased derivation has a unique exact signed Pauli correction.
The equivalence of completeness targets below is conditional and does not
assert general normalization in either presentation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d]

/-- Completeness of the explicit erased relation on canonical adjacent words. -/
def AdjacentSymplecticErasureComplete (g : (ZMod d)ˣ) : Prop :=
  ∀ u v : Word n, IsAdjacentWord u → IsAdjacentWord v →
    (∀ p, symplecticAction d u p = symplecticAction d v p) →
      AdjacentSymplecticDerives g u v

variable [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

@[simp] theorem adjacentSymplecticClassWord_signedPauliWord (p : SignedPauli d n) :
    adjacentSymplecticClassWord g (signedPauliWord p) (isAdjacentWord_signedPauliWord p) = 1 :=
  adjacentPresentedPauliSubgroup_le_symplectic_ker g
    (signedPauliWord_mem_adjacentPresentedPauliSubgroup g p)

/-- Every guarded erased derivation lifts to an exact one with unique signed
Pauli coordinates. All words in the derivation remain adjacent. -/
theorem adjacentSymplecticDerives_lift_unique {u v : Word n}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v)
    (h : AdjacentSymplecticDerives g u v) :
    ∃! p : SignedPauli d n, AdjacentDerives g u (signedPauliWord p ++ v) := by
  obtain ⟨q, hq, huv⟩ := (adjacentSymplecticDerives_iff_pauli_correction g u v hu hv).mp h
  rw [← AdjacentPauliWords.signedPauliToPresented_range] at hq
  obtain ⟨p, rfl⟩ := hq
  refine ⟨p, (adjacentClassWord_eq_iff_derives g _ _ hu
    ((isAdjacentWord_append _ _).mpr ⟨isAdjacentWord_signedPauliWord p, hv⟩)).mp huv, ?_⟩
  intro q hq
  apply AdjacentPauliWords.signedPauliToPresented_injective g
  have hq' := (adjacentClassWord_eq_iff_derives g _ _ hu
    ((isAdjacentWord_append _ _).mpr ⟨isAdjacentWord_signedPauliWord q, hv⟩)).mpr hq
  change adjacentClassWord g u hu =
    AdjacentPauliWords.signedPauliToPresented g q * adjacentClassWord g v hv at hq'
  exact mul_right_cancel (hq'.symm.trans huv)

/-- Equal exact matrices eliminate the residual Pauli correction using only
the already faithful adjacent Pauli subgroup. -/
theorem adjacentDerives_of_symplecticDerives_of_denote_eq {u v : Word n}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v)
    (hs : AdjacentSymplecticDerives g u v) (he : denote d u = denote d v) :
    AdjacentDerives g u v := by
  obtain ⟨q, hq, huv⟩ := (adjacentSymplecticDerives_iff_pauli_correction g u v hu hv).mp hs
  let e := adjacentPresentedToGenerated (n := n) (show Odd d from Fact.out) g
  have hUV : e (adjacentClassWord g u hu) = e (adjacentClassWord g v hv) :=
    Subtype.ext (Subtype.ext he)
  have hh := congrArg e huv
  rw [map_mul, hUV] at hh
  have hqone : e q = 1 := mul_right_cancel (hh.symm.trans (one_mul _).symm)
  have hq1 : q = 1 := AdjacentPauliWords.adjacentPresentedToGenerated_injOn_pauliSubgroup g hq
    (adjacentPresentedPauliSubgroup g).one_mem (by simpa only [map_one] using hqone)
  apply (adjacentClassWord_eq_iff_derives g _ _ hu hv).mp
  simpa only [hq1, one_mul] using huv

/-- Restricted erased completeness suffices for the paper's exact adjacent target. -/
theorem adjacentFigure1Complete_of_symplecticErasureComplete
    (hs : AdjacentSymplecticErasureComplete (n := n) g) :
    AdjacentFigure1Complete (n := n) g := by
  intro u v hu hv he
  apply adjacentDerives_of_symplecticDerives_of_denote_eq g hu hv _ he
  apply hs u v hu hv
  have hUV : generatedWord (d := d) u = generatedWord v := Subtype.ext (Subtype.ext he)
  have hf := congrArg (generatedSymplecticHom (show Odd d from Fact.out)) hUV
  intro p
  simpa only [generatedSymplecticHom_word] using
    congrArg (fun F : symplecticGroup d n => F.val p) hf

/-- Conversely, restricted exact completeness realizes the semantic Pauli
correction, after which the guarded erasure removes its literal adjacent word. -/
theorem adjacentSymplecticErasureComplete_of_figure1Complete
    (hc : AdjacentFigure1Complete (n := n) g) :
    AdjacentSymplecticErasureComplete (n := n) g := by
  intro u v hu hv huv
  let hd : Odd d := Fact.out
  have hF : generatedSymplecticHom hd (generatedWord u) =
      generatedSymplecticHom hd (generatedWord v) := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    simpa only [generatedSymplecticHom_word] using huv p
  have hk : generatedWord (d := d) u * (generatedWord v)⁻¹ ∈ (generatedSymplecticHom hd).ker := by
    change generatedSymplecticHom hd (generatedWord u * (generatedWord v)⁻¹) = 1
    simp only [map_mul, map_inv, hF, mul_inv_cancel]
  rw [generatedSymplecticHom_ker_eq_signedPauli_range] at hk
  obtain ⟨p, hp⟩ := hk
  have he : generatedWord (d := d) u = generatedWord (signedPauliWord p ++ v) := by
    rw [generatedWord_append]
    change generatedWord u = signedPauliToGenerated hd p * generatedWord v
    rw [hp]
    group
  have hpa : IsAdjacentWord (signedPauliWord p ++ v) :=
    (isAdjacentWord_append _ _).mpr ⟨isAdjacentWord_signedPauliWord p, hv⟩
  have hr := hc u (signedPauliWord p ++ v) hu hpa
    (congrArg (fun U : generatedCliffordGroup d n => U.val.val) he)
  apply (adjacentSymplecticClassWord_eq_iff_derives g _ _ hu hv).mp
  have hh := (adjacentSymplecticClassWord_eq_iff_derives g _ _ hu hpa).mpr
    (adjacentDerives_symplectic g hr)
  simpa only [adjacentSymplecticClassWord_append_certified,
    adjacentSymplecticClassWord_signedPauliWord, one_mul] using hh

/-- Exact adjacent completeness is equivalent to restricted erased completeness.
Neither side is assumed by this equivalence. -/
theorem adjacentFigure1Complete_iff_symplecticErasureComplete :
    AdjacentFigure1Complete (n := n) g ↔ AdjacentSymplecticErasureComplete (n := n) g :=
  ⟨adjacentSymplecticErasureComplete_of_figure1Complete g,
    adjacentFigure1Complete_of_symplecticErasureComplete g⟩

end QuditClifford.Circuit
