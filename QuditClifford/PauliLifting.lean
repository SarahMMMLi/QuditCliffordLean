import QuditClifford.PauliWordRewrites
import QuditClifford.SymplecticKernel
import QuditClifford.GeneratedScalarKernel

/-! # Concrete lifting of symplectic rewrites to exact Clifford rewrites

The Pauli subgroup of the named-wire Figure 1 helper presentation is normal and has a
faithful signed-Pauli normal form. Consequently every syntactic Pauli-erased
derivation lifts to an exact derivation with a unique signed Pauli correction.
For equal matrices that correction is trivial. The only completeness input
in the conditional equivalences below is normalization of the explicit
symplectic erasure relation. Source-restricted lifting additionally requires
these derivations to be replayed in `AdjacentDerives`.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

@[simp] theorem symplecticClassWord_signedPauliWord (p : SignedPauli d n) :
    symplecticClassWord g (signedPauliWord p) = 1 := by
  exact presentedPauliSubgroup_le_symplectic_ker g
    (signedPauliWord_mem_presentedPauliSubgroup g p)

/-- A symplectic rewrite admits a unique exact signed Pauli correction. Every
equality here is obtained from the displayed rewriting congruence. -/
theorem symplecticDerives_lift_unique {u v : Word n} (h : SymplecticDerives g u v) :
    ∃! p : SignedPauli d n, Derives g u (signedPauliWord p ++ v) := by
  obtain ⟨q, hq, huv⟩ := (symplecticDerives_iff_pauli_correction g u v).mp h
  rw [← signedPauliToPresented_range] at hq
  obtain ⟨p, rfl⟩ := hq
  refine ⟨p, (classWord_eq_iff_derives g _ _).mp huv, ?_⟩
  intro q hq
  apply signedPauliToPresented_injective g
  have hq' := (classWord_eq_iff_derives g _ _).mpr hq
  change classWord g u = signedPauliToPresented g q * classWord g v at hq'
  exact mul_right_cancel (hq'.symm.trans huv)

/-- An erased derivation between exactly equal matrices is an exact Figure 1
derivation. The residual Pauli vanishes by the already faithful Pauli subgroup. -/
theorem derives_of_symplecticDerives_of_denote_eq {u v : Word n}
    (hs : SymplecticDerives g u v) (he : denote d u = denote d v) : Derives g u v := by
  obtain ⟨q, hq, huv⟩ := (symplecticDerives_iff_pauli_correction g u v).mp hs
  let e := presentedToGenerated (n := n) (show Odd d from Fact.out) g
  have hUV : e (classWord g u) = e (classWord g v) := Subtype.ext (Subtype.ext he)
  have hh := congrArg e huv
  rw [map_mul, hUV] at hh
  have hqone : e q = 1 := mul_right_cancel (hh.symm.trans (one_mul _).symm)
  have hq1 : q = 1 := presentedToGenerated_injOn_pauliSubgroup g hq
    (presentedPauliSubgroup g).one_mem (by simpa only [map_one] using hqone)
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [hq1, one_mul] using huv

/-- The noncentral extension step is fully instantiated for the actual exact
and Pauli-erased rewrite presentations. No projective lifting hypothesis remains. -/
theorem figure1Complete_of_symplecticErasureComplete
    (hs : SymplecticErasureComplete (n := n) g) : Figure1Complete (n := n) g := by
  intro u v he
  apply derives_of_symplecticDerives_of_denote_eq g _ he
  apply hs u v
  have hu : generatedWord (d := d) u = generatedWord v := Subtype.ext (Subtype.ext he)
  have hf := congrArg (generatedSymplecticHom (show Odd d from Fact.out)) hu
  intro p
  simpa only [generatedSymplecticHom_word] using
    congrArg (fun F : symplecticGroup d n => F.val p) hf

/-- Conversely, exact completeness realizes the signed Pauli correction between
two words with equal exponent actions, then deletes it by the explicit erasures. -/
theorem symplecticErasureComplete_of_figure1Complete
    (hc : Figure1Complete (n := n) g) : SymplecticErasureComplete (n := n) g := by
  intro u v huv
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
  have hr := hc u (signedPauliWord p ++ v)
    (congrArg (fun U : generatedCliffordGroup d n => U.val.val) he)
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  have hh := (symplecticClassWord_eq_iff_derives g _ _).mpr (derives_symplectic g hr)
  simpa only [symplecticClassWord_append, symplecticClassWord_signedPauliWord, one_mul] using hh

/-- The exact Figure 1 target is equivalent to completeness of its explicit
symplectic erasure. This does not assert the remaining symplectic target. -/
theorem figure1Complete_iff_symplecticErasureComplete :
    Figure1Complete (n := n) g ↔ SymplecticErasureComplete (n := n) g :=
  ⟨symplecticErasureComplete_of_figure1Complete g,
    figure1Complete_of_symplecticErasureComplete g⟩

end QuditClifford.Circuit
