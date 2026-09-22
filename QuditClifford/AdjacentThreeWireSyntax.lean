import QuditClifford.AdjacentPresentedCircuit
import QuditClifford.AdjacentNormalCircuit

/-!
# Routing named three-wire circuits into the adjacent alphabet

The remote CZ letter is compiled into Figure 4 T7's actual SWAP expansion.
Compilation preserves exact matrices and fixes already-adjacent words. These
facts alone do not establish preservation of rewrite derivations.
-/
noncomputable section
namespace QuditClifford.Circuit

/-- The canonical adjacent realization of the remote CZ on wires zero and two. -/
def remoteThreeWord (d : ℕ) : Word 3 :=
  CIZ (d := d) 0 1 2 (by decide) (by decide) (by decide)

theorem isAdjacentWord_remoteThreeWord (d : ℕ) : IsAdjacentWord (remoteThreeWord d) := by
  unfold remoteThreeWord CIZ
  have hw : IsAdjacentWord (SWAP (d := d) (1 : Fin 3) 2 (by decide)) :=
    isAdjacentWord_SWAP_neighbor (1 : Fin 2)
  have hc : (Gate.CZ (0 : Fin 3) 1 (by decide)).IsAdjacent := ⟨.CZ 0, rfl⟩
  simp only [isAdjacentWord_append, isAdjacentWord_cons, isAdjacentWord_nil, and_true]
  exact ⟨⟨hw, hc⟩, hw⟩

/-- Route each primitive gate, orienting local CZ and expanding the remote one. -/
def routeThreeGate (d : ℕ) : Gate 3 → Word 3
  | .scalar => [.scalar]
  | .H i => [.H i]
  | .S i => [.S i]
  | .CZ i j _ =>
      if (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) then remoteThreeWord d
      else if i=0 ∨ j=0 then [.CZ 0 1 (by decide)] else [.CZ 1 2 (by decide)]

/-- Compile a named three-wire circuit by replacing its primitive letters. -/
def routeThreeWord (d : ℕ) (w : Word 3) : Word 3 := (w.map (routeThreeGate d)).flatten

@[simp] theorem routeThreeWord_nil (d : ℕ) : routeThreeWord d [] = [] := rfl
@[simp] theorem routeThreeWord_cons (d : ℕ) (a : Gate 3) (w : Word 3) :
    routeThreeWord d (a::w) = routeThreeGate d a ++ routeThreeWord d w := rfl
@[simp] theorem routeThreeWord_append (d : ℕ) (u v : Word 3) :
    routeThreeWord d (u++v) = routeThreeWord d u ++ routeThreeWord d v := by
  simp [routeThreeWord]
@[simp] theorem routeThreeWord_replicate (d k : ℕ) (a : Gate 3) :
    routeThreeWord d (List.replicate k a) = power (routeThreeGate d a) k := by
  simp [routeThreeWord, power]
@[simp] theorem routeThreeWord_power (d : ℕ) (w : Word 3) (k : ℕ) :
    routeThreeWord d (power w k) = power (routeThreeWord d w) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [power_succ, routeThreeWord_append, ih]

theorem routeThreeGate_isAdjacent (d : ℕ) (a : Gate 3) :
    IsAdjacentWord (routeThreeGate d a) := by
  cases a with
  | scalar => simp [routeThreeGate]
  | H i => simp [routeThreeGate]
  | S i => simp [routeThreeGate]
  | CZ i j hij =>
      simp only [routeThreeGate]
      split
      · exact isAdjacentWord_remoteThreeWord d
      · split
        · exact (isAdjacentWord_cons _ _).mpr ⟨⟨.CZ 0, rfl⟩, isAdjacentWord_nil⟩
        · exact (isAdjacentWord_cons _ _).mpr ⟨⟨.CZ 1, rfl⟩, isAdjacentWord_nil⟩

theorem routeThreeWord_isAdjacent (d : ℕ) (w : Word 3) :
    IsAdjacentWord (routeThreeWord d w) := by
  induction w with
  | nil => exact isAdjacentWord_nil
  | cons a w ih => exact (isAdjacentWord_append _ _).mpr ⟨routeThreeGate_isAdjacent d a, ih⟩

theorem routeThreeGate_eq_of_adjacent (d : ℕ) (a : Gate 3) (ha : a.IsAdjacent) :
    routeThreeGate d a = [a] := by
  obtain ⟨b, rfl⟩ := ha
  cases b with
  | scalar => rfl
  | H i => rfl
  | S i => rfl
  | CZ i => fin_cases i <;> simp [routeThreeGate, AdjacentGate.toGate]

/-- Routing is the identity on the paper's actual adjacent alphabet. -/
theorem routeThreeWord_eq_of_adjacent (d : ℕ) (w : Word 3) (hw : IsAdjacentWord w) :
    routeThreeWord d w = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [isAdjacentWord_cons] at hw
      rw [routeThreeWord_cons, routeThreeGate_eq_of_adjacent d a hw.1, ih hw.2]
      rfl

@[simp] theorem routeThreeWord_idempotent (d : ℕ) (w : Word 3) :
    routeThreeWord d (routeThreeWord d w) = routeThreeWord d w :=
  routeThreeWord_eq_of_adjacent _ _ (routeThreeWord_isAdjacent _ _)

variable {d : ℕ} [NeZero d] [Fact d.Prime]

/-- The routing implementation has exactly the intended primitive matrix. -/
theorem denote_routeThreeGate (hd : Odd d) (a : Gate 3) :
    denote d (routeThreeGate d a) = a.denote d := by
  cases a with
  | scalar => simp [routeThreeGate]
  | H i => simp [routeThreeGate]
  | S i => simp [routeThreeGate]
  | CZ i j hij =>
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      all_goals simp [routeThreeGate, remoteThreeWord, denote_CIZ hd, Gate.denote, mul_comm]
      all_goals intro x; congr 1; ring

/-- Exact matrix preservation of routing, including the selected scalar. -/
theorem denote_routeThreeWord (hd : Odd d) (w : Word 3) :
    denote d (routeThreeWord d w) = denote d w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [routeThreeWord_cons, denote_append, denote_routeThreeGate hd, ih]
      rfl

end QuditClifford.Circuit
