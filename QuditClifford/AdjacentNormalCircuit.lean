import QuditClifford.AdjacentCircuit
import QuditClifford.NormalCircuit

/-! # The concrete normal grammar compiles into the adjacent source alphabet -/
namespace QuditClifford.Circuit
variable {d n : ℕ}

@[simp] theorem isAdjacentWord_scalar (k : ℕ) : IsAdjacentWord (scalar (n := n) k) :=
  IsAdjacentWord.replicate Gate.isAdjacent_scalar k

@[simp] theorem isAdjacentWord_Sexp (i : Fin n) (a : ZMod d) : IsAdjacentWord (Sexp i a) :=
  IsAdjacentWord.replicate (Gate.isAdjacent_S i) a.val

@[simp] theorem isAdjacentWord_omegaPower (a : ZMod d) :
    IsAdjacentWord (omegaPower (n := n) a) := isAdjacentWord_scalar _

@[simp] theorem isAdjacentWord_X (i : Fin n) : IsAdjacentWord (X (d := d) i) := by
  simp [X]

@[simp] theorem isAdjacentWord_Z (i : Fin n) : IsAdjacentWord (Z (d := d) i) := by
  simp [Z]

@[simp] theorem isAdjacentWord_Xexp (i : Fin n) (a : ZMod d) : IsAdjacentWord (Xexp i a) :=
  (isAdjacentWord_X i).power a.val

@[simp] theorem isAdjacentWord_Zexp (i : Fin n) (a : ZMod d) : IsAdjacentWord (Zexp i a) :=
  (isAdjacentWord_Z i).power a.val

@[simp] theorem isAdjacentWord_multiplier [NeZero d] (i : Fin n) (a : (ZMod d)ˣ) :
    IsAdjacentWord (multiplier i a) := by
  simp [multiplier]

/-- Every neighboring CX expansion stays within the canonical adjacent alphabet. -/
theorem isAdjacentWord_CX_neighbor (i : Fin n) :
    IsAdjacentWord (CX i.castSucc i.succ (adjacent_ne i)) := by
  simp [CX, Gate.isAdjacent_CZ]

/-- Every neighboring SWAP expansion stays within the canonical adjacent alphabet. -/
theorem isAdjacentWord_SWAP_neighbor (i : Fin n) :
    IsAdjacentWord (SWAP (d := d) i.castSucc i.succ (adjacent_ne i)) := by
  simp only [SWAP, isAdjacentWord_append]
  refine ⟨isAdjacentWord_scalar _, IsAdjacentWord.power ?_ 3⟩
  simp [Gate.isAdjacent_CZ]

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [Fact d.Prime]

/-- Every A box uses only scalar and single-wire gates. -/
theorem ABox.toWord_isAdjacent (A : ABox (ZMod d)) (i : Fin n) :
    IsAdjacentWord (A.toWord i) := by
  unfold ABox.toWord
  split <;> simp

/-- Every E box uses only S on its named wire. -/
theorem eWord_isAdjacent (b : ZMod d) (i : Fin n) : IsAdjacentWord (eWord b i) :=
  isAdjacentWord_Sexp _ _

/-- A B box on neighboring wires compiles into the source alphabet. -/
theorem bWord_isAdjacent (a b : ZMod d) (i : Fin n) :
    IsAdjacentWord (bWord a b i.castSucc i.succ (adjacent_ne i)) := by
  have hs := isAdjacentWord_SWAP_neighbor (d := d) i
  have hx := isAdjacentWord_CX_neighbor i
  unfold bWord
  split <;> simp only [isAdjacentWord_append]
  · exact ⟨hs, hx.power _⟩
  · exact ⟨⟨⟨hs, hx.power _⟩, by simp⟩, isAdjacentWord_Sexp _ _⟩

/-- A D box on neighboring wires compiles into the source alphabet. -/
theorem dWord_isAdjacent (a b : ZMod d) (i : Fin n) :
    IsAdjacentWord (dWord a b i.castSucc i.succ (adjacent_ne i)) := by
  have hs := isAdjacentWord_SWAP_neighbor (d := d) i
  have hc := Gate.isAdjacent_CZ i (adjacent_ne i)
  unfold dWord
  split <;> simp only [isAdjacentWord_append]
  · exact ⟨hs, IsAdjacentWord.replicate hc _⟩
  · exact ⟨⟨⟨hs, IsAdjacentWord.replicate hc _⟩, by simp⟩, isAdjacentWord_Sexp _ _⟩

/-- The entire literal Z-normal sweep uses the canonical adjacent alphabet. -/
theorem ZNormal.toWord_isAdjacent {n : ℕ} (N : ZNormal (ZMod d) n) :
    IsAdjacentWord N.toWord := by
  induction N with
  | start A => exact A.toWord_isAdjacent _
  | @step n a b N ih =>
    apply (isAdjacentWord_append _ _).mpr
    exact ⟨bWord_isAdjacent a b (0 : Fin (n+1)), ih.shift⟩

/-- The entire literal X-normal sweep uses the canonical adjacent alphabet. -/
theorem XNormal.toWord_isAdjacent {n : ℕ} (N : XNormal (ZMod d) n) :
    IsAdjacentWord N.toWord := by
  induction N with
  | finish c => exact eWord_isAdjacent _ _
  | @step n a b N ih =>
    apply (isAdjacentWord_append _ _).mpr
    exact ⟨ih.shift, dWord_isAdjacent a b (0 : Fin (n+1))⟩

/-- Every recursively compiled normal word lies in the source's adjacent alphabet. -/
theorem SymplecticNormalForm.toWord_isAdjacent {n : ℕ}
    (N : SymplecticNormalForm (ZMod d) n) : IsAdjacentWord N.toWord := by
  induction N with
  | empty => exact isAdjacentWord_nil
  | step Z X N ih =>
    exact (isAdjacentWord_append _ _).mpr
      ⟨(isAdjacentWord_append _ _).mpr ⟨ih.initial, X.toWord_isAdjacent⟩, Z.toWord_isAdjacent⟩

end QuditClifford.NormalBoxes
