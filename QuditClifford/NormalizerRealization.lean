import QuditClifford.GeneratedRealization

/-! # Realization of the full unitary normalizer up to phase

The generated exact Clifford group has only the finite scalar group selected
by Figure 1. The full unitary Pauli normalizer permits arbitrary unit-modulus
complex scalars. Every member of the latter is a scalar multiple of an actual
primitive circuit, and their quotients by their respective scalar kernels
are isomorphic.
-/
noncomputable section
namespace QuditClifford
open Matrix
variable {d n : ℕ} [NeZero d]

/-- A scalar relating two unitary matrices necessarily has modulus one. -/
theorem norm_eq_one_of_unitary_smul {U V : QuditOperator d n}
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ)
    (c : ℂ) (h : U = c • V) : ‖c‖ = 1 := by
  have hh : Uᴴ * U = 1 := hU.1
  rw [h, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    show Vᴴ * V = 1 from hV.1, smul_smul] at hh
  have hc : star c * c = 1 := by
    have he := congrArg (fun A : QuditOperator d n => A 0 0) hh
    simpa using he
  have hn := congrArg norm hc
  simp only [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg c]

/-- The complete Pauli action of the full normalizer has exactly the scalar kernel. -/
theorem mem_normalizerConjugationHom_ker_iff_scalar (U : cliffordMatrixGroup d n) :
    U ∈ (normalizerConjugationHom : cliffordMatrixGroup d n →*
      Pauli.scalarFixingAut d n).ker ↔
      ∃ c : ℂ, U.val.val = c • (1 : QuditOperator d n) := by
  change normalizerConjugationHom U = 1 ↔ _
  constructor
  · intro h
    apply (pauli_centralizer U.val.val).mp
    intro p
    have hp := repr_pauliConjugationAut U.val.val U.val.property U.property p
    have he := congrArg (fun f : Pauli.scalarFixingAut d n => f.val p) h
    change pauliConjugationAut U.val.val U.val.property U.property p = p at he
    rw [he] at hp
    calc
      _ = (U.val.val * Pauli.repr p * U.val.valᴴ) * U.val.val := by
        rw [mul_assoc, mul_assoc, show U.val.valᴴ * U.val.val = 1 from U.val.property.1,
          mul_one]
      _ = _ := congrArg (fun A => A * U.val.val) hp.symm
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro p
    apply Pauli.repr_injective
    change Pauli.repr (pauliConjugationAut U.val.val U.val.property U.property p) = Pauli.repr p
    rw [repr_pauliConjugationAut]
    have hcomm : U.val.val * Pauli.repr p = Pauli.repr p * U.val.val := by
      rw [hc]
      simp
    rw [hcomm, mul_assoc, show U.val.val * U.val.valᴴ = 1 from U.val.property.2, mul_one]

/-- In the full unitary normalizer its scalar kernel consists of unit-modulus phases. -/
theorem mem_normalizerConjugationHom_ker_iff_phase (U : cliffordMatrixGroup d n) :
    U ∈ (normalizerConjugationHom : cliffordMatrixGroup d n →*
      Pauli.scalarFixingAut d n).ker ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ U.val.val = c • (1 : QuditOperator d n) := by
  rw [mem_normalizerConjugationHom_ker_iff_scalar]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, norm_eq_one_of_unitary_smul U.val.property
      (Matrix.unitaryGroup _ ℂ).one_mem c hc, hc⟩
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

namespace Circuit
variable [Fact d.Prime]

/-- Every unitary Pauli normalizer is a unit-modulus scalar times an actual
primitive circuit in the exact generated group. -/
theorem normalizer_eq_phase_smul_word (hd : Odd d) (U : cliffordMatrixGroup d n) :
    ∃ (c : ℂ) (w : Word n), ‖c‖ = 1 ∧ U.val.val = c • denote d w := by
  obtain ⟨V, hV⟩ := generatedPauliAutHom_surjective hd (normalizerConjugationHom U)
  obtain ⟨w, rfl⟩ := generatedWord_surjective hd V
  have ha : ∀ p : Pauli d n,
      denote d w * Pauli.repr p * (denote d w)ᴴ =
        U.val.val * Pauli.repr p * U.val.valᴴ := by
    intro p
    calc
      _ = Pauli.repr ((generatedPauliAutHom hd (generatedWord w)).val p) :=
        (generatedPauliAutHom_matrix hd (generatedWord w) p).symm
      _ = Pauli.repr ((normalizerConjugationHom U).val p) :=
        congrArg (fun f : Pauli.scalarFixingAut d n => Pauli.repr (f.val p)) hV
      _ = _ := repr_pauliConjugationAut U.val.val U.val.property U.property p
  obtain ⟨c, _, hc⟩ := unitary_projectiveEq_of_same_pauli_action
    (denote d w) U.val.val (denote_unitary w) U.val.property ha
  exact ⟨c, w, norm_eq_one_of_unitary_smul U.val.property (denote_unitary w) c hc, hc⟩

/-- Among unitary matrices, normalizing the Paulis is equivalent to being a
unit-modulus scalar multiple of a primitive Clifford circuit. -/
theorem normalizesPaulis_iff_phase_smul_word (hd : Odd d)
    (U : Matrix.unitaryGroup (Pauli.Basis d n) ℂ) :
    NormalizesPaulis U.val ↔ ∃ (c : ℂ) (w : Word n),
      ‖c‖ = 1 ∧ U.val = c • denote d w := by
  constructor
  · intro hU
    exact normalizer_eq_phase_smul_word hd ⟨U, hU⟩
  · rintro ⟨c, w, hc, hU⟩ p
    obtain ⟨q, hq⟩ := denote_normalizes hd w p
    refine ⟨q, ?_⟩
    have hcstar : c * star c = 1 := by
      simpa [hc] using Complex.mul_conj' c
    rw [hU, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hcstar, one_smul]
    exact hq

/-- The full unitary normalizer modulo all its scalar matrices realizes exactly
the scalar-fixing automorphisms of the finite Pauli group. -/
def normalizerQuotientScalarsEquiv (hd : Odd d) :
    cliffordMatrixGroup d n ⧸ (normalizerConjugationHom : cliffordMatrixGroup d n →*
      Pauli.scalarFixingAut d n).ker ≃* Pauli.scalarFixingAut d n :=
  QuotientGroup.quotientKerEquivOfSurjective _ (normalizerConjugationHom_surjective hd)

/-- The full and generated Clifford groups have isomorphic projective quotients,
although their exact scalar subgroups differ. -/
def normalizerQuotientScalarsEquivGenerated (hd : Odd d) :
    cliffordMatrixGroup d n ⧸ (normalizerConjugationHom : cliffordMatrixGroup d n →*
      Pauli.scalarFixingAut d n).ker ≃*
      generatedCliffordGroup d n ⧸ (generatedPauliAutHom hd).ker :=
  (normalizerQuotientScalarsEquiv hd).trans (generatedQuotientScalarsEquiv hd).symm

end Circuit
end QuditClifford
