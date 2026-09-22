import QuditClifford.GeneratedRealization
import QuditClifford.GeneratedScalarKernel
import QuditClifford.SymplecticCounting

/-! # Unique exact normal forms for generated Clifford matrices

The normal form consists of a signed Pauli correction followed, in matrix
order, by the paper's concrete compiled symplectic normal form. Thus its scalar
convention is exactly Figure 1's -omega extension. This proves matrix normal
form existence and uniqueness; derivability of normalization using the rewrite
relations remains a separate obligation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
open NormalBoxes

/-- Exact normal data retains the independent sign and all ordinary Pauli phases. -/
abbrev ExactNormalData (d n : ℕ) [Fact d.Prime] :=
  SignedPauli d n × SymplecticNormalForm (ZMod d) n

/-- The actual primitive circuit for the exact normal data. -/
def exactNormalWord (N : ExactNormalData d n) : Word n :=
  signedPauliWord N.1 ++ N.2.toWord

/-- The exact matrix group element of the normal circuit. -/
def exactNormalMatrix (hd : Odd d) (N : ExactNormalData d n) : generatedCliffordGroup d n :=
  signedPauliToGenerated hd N.1 * generatedWord N.2.toWord

@[simp] theorem generatedWord_exactNormalWord (hd : Odd d) (N : ExactNormalData d n) :
    generatedWord (exactNormalWord N) = exactNormalMatrix hd N := by
  rw [exactNormalWord, generatedWord_append]
  rfl

@[simp] theorem generatedSymplecticHom_signedPauli (hd : Odd d) (p : SignedPauli d n) :
    generatedSymplecticHom hd (signedPauliToGenerated hd p) = 1 := by
  change signedPauliToGenerated hd p ∈ (generatedSymplecticHom hd).ker
  rw [generatedSymplecticHom_ker_eq_signedPauli_range]
  exact ⟨p, rfl⟩

/-- The compiled normal form induces exactly its proved symplectic equivalence. -/
theorem generatedSymplecticHom_normal (hd : Odd d)
    (N : SymplecticNormalForm (ZMod d) n) :
    generatedSymplecticHom hd (generatedWord N.toWord) = toPhaseSymplectic N.equiv := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [generatedSymplecticHom_word, N.toWord_symplecticAction]

@[simp] theorem exactNormalMatrix_symplectic (hd : Odd d) (N : ExactNormalData d n) :
    generatedSymplecticHom hd (exactNormalMatrix hd N) = toPhaseSymplectic N.2.equiv := by
  rw [exactNormalMatrix, map_mul, generatedSymplecticHom_signedPauli, one_mul,
    generatedSymplecticHom_normal]

/-- Distinct concrete symplectic labels or signed Pauli corrections give distinct matrices. -/
theorem exactNormalMatrix_injective (hd : Odd d) :
    Function.Injective (exactNormalMatrix (d := d) (n := n) hd) := by
  rintro ⟨p, N⟩ ⟨q, M⟩ h
  have hF := congrArg (generatedSymplecticHom hd) h
  simp only [exactNormalMatrix_symplectic] at hF
  have hNM : N = M := SymplecticNormalForm.equiv_injective
    (wireSymplecticEquiv.injective hF)
  cases hNM
  have hpq : p = q := signedPauliToGenerated_injective hd (mul_right_cancel h)
  exact Prod.ext hpq rfl

/-- Every exact generated Clifford matrix has the paper's actual normal circuit. -/
theorem exactNormalMatrix_surjective (hd : Odd d) :
    Function.Surjective (exactNormalMatrix (d := d) (n := n) hd) := by
  intro U
  obtain ⟨N, hN, _⟩ := SymplecticNormalForm.existsUnique_equiv
    (fromPhaseSymplectic (generatedSymplecticHom hd U))
  have hF : generatedSymplecticHom hd (generatedWord N.toWord) = generatedSymplecticHom hd U := by
    rw [generatedSymplecticHom_normal, hN]
    exact wireSymplecticEquiv.right_inv _
  let V := U * (generatedWord N.toWord)⁻¹
  have hV : V ∈ (generatedSymplecticHom hd).ker := by
    change generatedSymplecticHom hd V = 1
    simp [V, hF]
  rw [generatedSymplecticHom_ker_eq_signedPauli_range] at hV
  obtain ⟨p, hp⟩ := hV
  refine ⟨(p, N), ?_⟩
  change signedPauliToGenerated hd p * generatedWord N.toWord = U
  rw [hp]
  simp [V, mul_assoc]

/-- The bijection is obtained from actual compiled matrices, not a chosen semantic quotient. -/
def exactNormalEquiv (hd : Odd d) : ExactNormalData d n ≃ generatedCliffordGroup d n :=
  Equiv.ofBijective (exactNormalMatrix hd)
    ⟨exactNormalMatrix_injective hd, exactNormalMatrix_surjective hd⟩

/-- Proposition 3.13 with Figure 1's exact enlarged scalar convention. -/
theorem existsUnique_exactNormalForm (hd : Odd d) (U : generatedCliffordGroup d n) :
    ∃! N : ExactNormalData d n, exactNormalMatrix hd N = U := by
  obtain ⟨N, hN⟩ := exactNormalMatrix_surjective hd U
  exact ⟨N, hN, fun M hM => exactNormalMatrix_injective hd (hM.trans hN.symm)⟩

/-- Every primitive word has a unique exact matrix-equal normal word. This is
semantic normalization; no claim of a Figure 1 derivation is made here. -/
theorem existsUnique_exactNormalWord (hd : Odd d) (w : Word n) :
    ∃! N : ExactNormalData d n, denote d (exactNormalWord N) = denote d w := by
  obtain ⟨N, hN, huniq⟩ := existsUnique_exactNormalForm hd (generatedWord w)
  have he (M : ExactNormalData d n) :
      exactNormalMatrix hd M = generatedWord w ↔ denote d (exactNormalWord M) = denote d w := by
    rw [← generatedWord_exactNormalWord]
    exact ⟨fun h => congrArg (fun U : generatedCliffordGroup d n => U.val.val) h,
      fun h => Subtype.ext (Subtype.ext h)⟩
  exact ⟨N, (he N).mp hN, fun M hM => huniq M ((he M).mpr hM)⟩

/-- The enlarged Pauli subgroup is normal in the actual generated Clifford group. -/
instance signedPauli_range_normal (hd : Odd d) : (signedPauliToGenerated (n := n) hd).range.Normal := by
  rw [← generatedSymplecticHom_ker_eq_signedPauli_range hd]
  infer_instance

/-- Theorem 2.27 for the selected exact group and its enlarged signed Pauli subgroup. -/
def generatedQuotientSignedPauliEquiv (hd : Odd d) :
    generatedCliffordGroup d n ⧸ (signedPauliToGenerated hd).range ≃* symplecticGroup d n :=
  (QuotientGroup.quotientMulEquivOfEq
    (generatedSymplecticHom_ker_eq_signedPauli_range (n := n) hd).symm).trans
      (generatedQuotientKernelEquivSymplectic hd)

/-- Exact generated Clifford cardinality, including Figure 1's additional sign. -/
theorem generatedCliffordGroup_card (hd : Odd d) :
    Nat.card (generatedCliffordGroup d n) =
      2 * d ^ (n^2+2*n+1) * ∏ i ∈ Finset.range n, (d^(2*(i+1))-1) := by
  rw [← Nat.card_congr (exactNormalEquiv (n := n) hd)]
  change Nat.card (SignedPauli d n × SymplecticNormalForm (ZMod d) n) = _
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := SignedPauli d n),
    SignedPauli.card, SymplecticNormalForm.card]
  simp only [ZMod.card]
  rw [show n^2+2*n+1 = (2*n+1)+n^2 by omega, pow_add]
  ring

end QuditClifford.Circuit
