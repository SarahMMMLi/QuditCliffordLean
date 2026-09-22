import QuditClifford.PauliExactSequence
import QuditClifford.Projective

/-! # From actual matrix normalizers to the symplectic action

A unitary which conjugates Pauli matrices to Pauli matrices induces an actual
scalar-fixing Pauli automorphism. Its symplectic action and its projective-Pauli
kernel follow from faithful matrix interpretation. No realization of arbitrary
symplectic maps by primitive circuit words is presumed here.
-/
noncomputable section
namespace QuditClifford
open Matrix
variable {d n : ℕ} [NeZero d]

/-- The concrete normalizer condition on complex matrices. Forward preservation
suffices because the Pauli group is finite and unitary conjugation is injective. -/
def NormalizesPaulis (U : QuditOperator d n) : Prop :=
  ∀ p : Pauli d n, ∃ q : Pauli d n, U * Pauli.repr p * Uᴴ = Pauli.repr q

/-- Unitary conjugation preserves products exactly. -/
theorem unitary_conjugation_mul (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (A B : QuditOperator d n) :
    U * (A * B) * Uᴴ = (U * A * Uᴴ) * (U * B * Uᴴ) := by
  calc
    U * (A * B) * Uᴴ = (U * A) * (Uᴴ * U) * (B * Uᴴ) := by
      rw [show Uᴴ * U = 1 from hU.1]
      simp only [mul_one, mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- Unitary conjugation can be undone by conjugating with the adjoint. -/
theorem unitary_conjugation_cancel (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (A : QuditOperator d n) :
    Uᴴ * (U * A * Uᴴ) * U = A := by
  calc
    _ = (Uᴴ * U) * A * (Uᴴ * U) := by simp only [mul_assoc]
    _ = A := by rw [show Uᴴ * U = 1 from hU.1]; simp

/-- The chosen Pauli image is unique by faithfulness of the representation. -/
def normalizerPauliMap (U : QuditOperator d n) (hN : NormalizesPaulis U) (p : Pauli d n) :
    Pauli d n := Classical.choose (hN p)

@[simp] theorem repr_normalizerPauliMap (U : QuditOperator d n)
    (hN : NormalizesPaulis U) (p : Pauli d n) :
    Pauli.repr (normalizerPauliMap U hN p) = U * Pauli.repr p * Uᴴ :=
  (Classical.choose_spec (hN p)).symm

/-- Actual conjugation gives a homomorphism of the faithful Pauli coordinates. -/
def normalizerPauliHom (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    Pauli d n →* Pauli d n where
  toFun := normalizerPauliMap U hN
  map_one' := by
    apply Pauli.repr_injective
    rw [repr_normalizerPauliMap, Pauli.repr_one, mul_one]
    exact hU.2
  map_mul' p q := by
    apply Pauli.repr_injective
    simp only [repr_normalizerPauliMap, Pauli.repr_mul]
    exact unitary_conjugation_mul U hU _ _

/-- Injectivity is inherited from unitary conjugation, not assumed. -/
theorem normalizerPauliHom_injective (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    Function.Injective (normalizerPauliHom U hU hN) := by
  intro p q hpq
  apply Pauli.repr_injective
  have he := congrArg Pauli.repr hpq
  change Pauli.repr (normalizerPauliMap U hN p) =
    Pauli.repr (normalizerPauliMap U hN q) at he
  simp only [repr_normalizerPauliMap] at he
  have hh := congrArg (fun M : QuditOperator d n => Uᴴ * M * U) he
  simpa only [unitary_conjugation_cancel U hU] using hh

/-- The induced Pauli map is bijective because the Pauli group is finite. -/
def pauliConjugationAut (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    MulAut (Pauli d n) :=
  MulEquiv.ofBijective (normalizerPauliHom U hU hN)
    ⟨normalizerPauliHom_injective U hU hN,
      (Finite.surjective_of_injective (normalizerPauliHom_injective U hU hN))⟩

@[simp] theorem repr_pauliConjugationAut (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U)
    (p : Pauli d n) :
    Pauli.repr (pauliConjugationAut U hU hN p) = U * Pauli.repr p * Uᴴ :=
  repr_normalizerPauliMap U hN p

/-- Abstract scalar Paulis denote the corresponding scalar matrices. -/
theorem repr_pauli_scalar (c : ZMod d) :
    Pauli.repr (Pauli.scalar c : Pauli d n) = phase d c • (1 : QuditOperator d n) := by
  classical
  ext row col
  simp only [Pauli.repr, Pauli.scalar_x, add_zero, Pauli.scalar_phase,
    Pauli.scalar_z, dot_zero_left, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp

/-- Matrix conjugation fixes each scalar exactly. -/
theorem pauliConjugationAut_fixesScalars (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    Pauli.FixesScalars (pauliConjugationAut U hU hN) := by
  intro c
  apply Pauli.repr_injective
  rw [repr_pauliConjugationAut, repr_pauli_scalar]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one,
    show U * Uᴴ = 1 from hU.2]

/-- The symplectic action is induced by the actual unitary's conjugation of
Pauli matrices; it is not a definition identifying Cliffords with symplectic maps. -/
def cliffordSymplecticAction (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    symplecticGroup d n :=
  Pauli.symplecticAction (pauliConjugationAut U hU hN)
    (pauliConjugationAut_fixesScalars U hU hN)

/-- Trivial exponent action of an actual matrix normalizer is precisely inner
Pauli conjugation at the level of its complete conjugation action. -/
theorem normalizer_trivial_action_iff (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    (∀ p, (pauliConjugationAut U hU hN p).coords = p.coords) ↔
      ∃ q : Pauli d n, ∀ p : Pauli d n,
        U * Pauli.repr p * Uᴴ = Pauli.repr (q * p * q⁻¹) := by
  rw [Pauli.trivial_action_iff_inner _ (pauliConjugationAut_fixesScalars U hU hN)]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, fun p => ?_⟩
    rw [← repr_pauliConjugationAut, hq]
    rfl
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply MulEquiv.ext
    intro p
    apply Pauli.repr_injective
    rw [repr_pauliConjugationAut, hq]
    rfl

/-- The kernel of the concrete normalizer's exponent action consists of matrices
projectively equal to a Pauli. This conclusion uses the proved scalar centralizer. -/
theorem projective_pauli_of_trivial_action (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U)
    (h : ∀ p, (pauliConjugationAut U hU hN p).coords = p.coords) :
    ∃ q : Pauli d n, ProjectiveEq U (Pauli.repr q) := by
  obtain ⟨q, hq⟩ := (normalizer_trivial_action_iff U hU hN).mp h
  refine ⟨q, ProjectiveEq.symm ?_⟩
  apply projectiveEq_of_same_pauli_action U (Pauli.repr q) Uᴴ (Pauli.repr q⁻¹)
    hU.1 hU.2
  · rw [← Pauli.repr_mul, inv_mul_cancel, Pauli.repr_one]
  · intro p
    rw [hq, Pauli.repr_mul, Pauli.repr_mul]

/-- A unitary projectively equal to a Pauli has the corresponding exact inner
conjugation action, since its scalar cancels against the unitary inverse. -/
theorem trivial_action_of_projective_pauli (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U)
    (q : Pauli d n) (h : ProjectiveEq U (Pauli.repr q)) :
    ∀ p, (pauliConjugationAut U hU hN p).coords = p.coords := by
  apply (normalizer_trivial_action_iff U hU hN).mpr
  refine ⟨q, fun p => ?_⟩
  obtain ⟨c, _, hc⟩ := h
  have hp : U * Pauli.repr p = Pauli.repr (q * p * q⁻¹) * U := by
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, ← Pauli.repr_mul, ← Pauli.repr_mul]
    congr 2
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [hp, mul_assoc, show U * Uᴴ = 1 from hU.2, mul_one]

/-- The projective-Pauli kernel theorem for actual unitary matrix normalizers,
with both directions proved and no Clifford realization assumption. -/
theorem normalizer_trivial_action_iff_projective_pauli (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    (∀ p, (pauliConjugationAut U hU hN p).coords = p.coords) ↔
      ∃ q : Pauli d n, ProjectiveEq U (Pauli.repr q) := by
  constructor
  · exact projective_pauli_of_trivial_action U hU hN
  · rintro ⟨q, hq⟩
    exact trivial_action_of_projective_pauli U hU hN q hq

/-- The symplectic identity is exactly trivial action on all Pauli exponents. -/
theorem cliffordSymplecticAction_eq_one_iff (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    cliffordSymplecticAction U hU hN = 1 ↔
      ∀ p, (pauliConjugationAut U hU hN p).coords = p.coords := by
  constructor
  · intro h p
    have hh := congrArg (fun F : symplecticGroup d n => F.1 p.coords) h
    change Pauli.action (pauliConjugationAut U hU hN) p.coords = p.coords at hh
    rwa [Pauli.action_coords _ (pauliConjugationAut_fixesScalars U hU hN)] at hh
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change Pauli.action (pauliConjugationAut U hU hN) v = v
    exact h (Pauli.representative v)

/-- The kernel of the genuine matrix normalizer's symplectic action consists
exactly of matrices equal to a Pauli up to a nonzero complex scalar. -/
theorem cliffordSymplecticAction_kernel (U : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    cliffordSymplecticAction U hU hN = 1 ↔
      ∃ q : Pauli d n, ProjectiveEq U (Pauli.repr q) := by
  rw [cliffordSymplecticAction_eq_one_iff,
    normalizer_trivial_action_iff_projective_pauli]

@[simp] theorem NormalizesPaulis.one : NormalizesPaulis (1 : QuditOperator d n) := by
  intro p
  exact ⟨p, by simp⟩

/-- The concrete normalizer condition is closed under sequential composition. -/
theorem NormalizesPaulis.mul {U V : QuditOperator d n}
    (hU : NormalizesPaulis U) (hV : NormalizesPaulis V) : NormalizesPaulis (U * V) := by
  intro p
  obtain ⟨q, hq⟩ := hV p
  obtain ⟨r, hr⟩ := hU q
  refine ⟨r, ?_⟩
  calc
    _ = U * (V * Pauli.repr p * Vᴴ) * Uᴴ := by
      simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = Pauli.repr r := by rw [hq, hr]

/-- Inverse closure follows from the proved finite bijective conjugation action. -/
theorem NormalizesPaulis.adjoint {U : QuditOperator d n}
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ) (hN : NormalizesPaulis U) :
    NormalizesPaulis Uᴴ := by
  intro p
  let φ := pauliConjugationAut U hU hN
  refine ⟨φ.symm p, ?_⟩
  have hp : Pauli.repr p = U * Pauli.repr (φ.symm p) * Uᴴ := by
    have hh := repr_pauliConjugationAut U hU hN (φ.symm p)
    change Pauli.repr (φ (φ.symm p)) = _ at hh
    simpa only [φ.apply_symm_apply] using hh
  rw [Matrix.conjTranspose_conjTranspose, hp, unitary_conjugation_cancel U hU]

/-- The genuine unitary matrix normalizer of the finite Pauli matrices. -/
def cliffordMatrixGroup (d n : ℕ) [NeZero d] :
    Subgroup (Matrix.unitaryGroup (Pauli.Basis d n) ℂ) where
  carrier U := NormalizesPaulis U.val
  one_mem' := NormalizesPaulis.one
  mul_mem' := fun hU hV => hU.mul hV
  inv_mem' := fun {U} hU => hU.adjoint U.property

/-- Identity conjugation induces the identity Pauli automorphism. -/
theorem pauliConjugationAut_one :
    pauliConjugationAut (1 : QuditOperator d n)
      (Matrix.unitaryGroup _ ℂ).one_mem NormalizesPaulis.one = 1 := by
  apply MulEquiv.ext
  intro p
  apply Pauli.repr_injective
  rw [repr_pauliConjugationAut]
  simp

/-- Composition of actual unitaries composes their induced Pauli automorphisms. -/
theorem pauliConjugationAut_mul (U V : QuditOperator d n)
    (hU : U ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Pauli.Basis d n) ℂ)
    (hN : NormalizesPaulis U) (hM : NormalizesPaulis V) :
    pauliConjugationAut (U * V) ((Matrix.unitaryGroup _ ℂ).mul_mem hU hV) (hN.mul hM) =
      pauliConjugationAut U hU hN * pauliConjugationAut V hV hM := by
  apply MulEquiv.ext
  intro p
  apply Pauli.repr_injective
  change Pauli.repr (pauliConjugationAut (U * V) _ _ p) =
    Pauli.repr (pauliConjugationAut U hU hN (pauliConjugationAut V hV hM p))
  simp only [repr_pauliConjugationAut, Matrix.conjTranspose_mul, mul_assoc]

/-- The concrete matrix normalizer acts homomorphically on Pauli coordinates,
fixing all scalars. Surjectivity is not part of this construction. -/
def normalizerConjugationHom : cliffordMatrixGroup d n →* Pauli.scalarFixingAut d n where
  toFun U := ⟨pauliConjugationAut U.val.val U.val.property U.property,
    pauliConjugationAut_fixesScalars U.val.val U.val.property U.property⟩
  map_one' := Subtype.ext pauliConjugationAut_one
  map_mul' U V := Subtype.ext (pauliConjugationAut_mul U.val.val V.val.val
    U.val.property V.val.property U.property V.property)

/-- The genuine matrix normalizer's symplectic action as a group homomorphism.
Its codomain is the symplectic group constructed from the paper's bilinear form. -/
def cliffordSymplecticHom : cliffordMatrixGroup d n →* symplecticGroup d n :=
  Pauli.actionHom.comp normalizerConjugationHom

@[simp] theorem cliffordSymplecticHom_apply (U : cliffordMatrixGroup d n) :
    cliffordSymplecticHom U =
      cliffordSymplecticAction U.val.val U.val.property U.property := rfl

/-- Membership in the actual matrix normalizer's symplectic kernel is exactly
projective equality to a Pauli matrix. -/
theorem mem_cliffordSymplecticHom_ker_iff (U : cliffordMatrixGroup d n) :
    U ∈ (cliffordSymplecticHom : cliffordMatrixGroup d n →* symplecticGroup d n).ker ↔
      ∃ q : Pauli d n, ProjectiveEq U.val.val (Pauli.repr q) := by
  change cliffordSymplecticAction U.val.val U.val.property U.property = 1 ↔ _
  exact cliffordSymplecticAction_kernel _ _ _

end QuditClifford
