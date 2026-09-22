import QuditClifford.AdjacentNormalCircuit
import QuditClifford.ExactNormalization

/-!
# Exact canonical words lie in the adjacent source alphabet

The independent sign and the ordinary Pauli phases compile to scalar and
single-wire letters. Combining them with the proved adjacent symplectic
normal grammar therefore gives an adjacent exact normal word. This establishes
alphabet membership only; deriving a word's normalization is a separate theorem.
-/
namespace QuditClifford.Circuit
variable {d n : ℕ}

/-- The expanded tensor product of shifts uses only single-wire gates. -/
theorem isAdjacentWord_allX (x : Pauli.Basis d n) : IsAdjacentWord (allX x) := by
  intro a ha
  obtain ⟨w, hw, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
  exact isAdjacentWord_Xexp i (x i) a ha

/-- The expanded tensor product of clocks uses only single-wire gates. -/
theorem isAdjacentWord_allZ (z : Pauli.Basis d n) : IsAdjacentWord (allZ z) := by
  intro a ha
  obtain ⟨w, hw, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw
  exact isAdjacentWord_Zexp i (z i) a ha

/-- Every ordinary Pauli word lies in the canonical adjacent alphabet. -/
theorem isAdjacentWord_pauliWord (p : Pauli d n) : IsAdjacentWord (pauliWord p) := by
  simp only [pauliWord, isAdjacentWord_append]
  exact ⟨⟨isAdjacentWord_omegaPower _, isAdjacentWord_allX _⟩, isAdjacentWord_allZ _⟩

/-- The extra Figure 1 sign uses only the exact scalar letter. -/
theorem isAdjacentWord_signedPauliWord (p : SignedPauli d n) :
    IsAdjacentWord (signedPauliWord p) := by
  simp only [signedPauliWord, isAdjacentWord_append]
  exact ⟨isAdjacentWord_scalar _, isAdjacentWord_pauliWord _⟩

variable [Fact d.Prime]

/-- Every exact normal word is a word in the paper's adjacent generating alphabet. -/
theorem exactNormalWord_isAdjacent (N : ExactNormalData d n) :
    IsAdjacentWord (exactNormalWord N) :=
  (isAdjacentWord_append _ _).mpr
    ⟨isAdjacentWord_signedPauliWord N.1, N.2.toWord_isAdjacent⟩

/-- The canonical exact matrix normalizer always returns an adjacent word,
even when its input uses the broader named-wire syntax. -/
theorem normalizeWord_isAdjacent (hd : Odd d) (w : Word n) :
    IsAdjacentWord (normalizeWord hd w) := exactNormalWord_isAdjacent _

end QuditClifford.Circuit
