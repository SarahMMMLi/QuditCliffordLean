import QuditClifford.Figure9Syntax

/-!
# Alphabet invariants of Figure 9 derivations

The contextual closure preserves adjacency and absence of scalar letters.
In particular, scalar erasure is a change of source alphabet, not a hidden
additional generating equation of the eighteen-rule presentation.
-/
namespace QuditClifford.Circuit
variable {d n : ℕ}

@[simp] theorem scalar_not_mem_eraseScalar (w : Word n) :
    Gate.scalar ∉ eraseScalar w := by
  induction w with
  | nil => simp
  | cons a w ih => cases a <;> simp [ih]

/-- Scalar-free words are exactly the fixed points of scalar erasure. -/
theorem eraseScalar_eq_self_iff (w : Word n) : eraseScalar w = w ↔ Gate.scalar ∉ w := by
  constructor
  · intro h
    rw [← h]
    exact scalar_not_mem_eraseScalar w
  · induction w with
    | nil => intro _; rfl
    | cons a w ih =>
        intro h
        cases a <;> simp_all

/-- Scalar freedom of a sequential composition is equivalent to freedom of each part. -/
theorem eraseScalar_append_eq_self_iff (u v : Word n) :
    eraseScalar (u ++ v) = u ++ v ↔ eraseScalar u = u ∧ eraseScalar v = v := by
  simp only [eraseScalar_eq_self_iff, List.mem_append, not_or]

variable [NeZero d]

/-- Figure 9 contextual rewriting cannot introduce a nonadjacent primitive. -/
theorem Figure9Derives.isAdjacent_iff (g : (ZMod d)ˣ) {u v : Word n}
    (h : Figure9Derives g u v) : IsAdjacentWord u ↔ IsAdjacentWord v := by
  induction h with
  | refl w => rfl
  | rule h => exact iff_of_true h.2.1 h.2.2.1
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | context l r h ih => simp only [isAdjacentWord_append, ih]

/-- Scalar-free endpoints remain scalar-free throughout the contextual closure. -/
theorem Figure9Derives.eraseScalar_iff (g : (ZMod d)ˣ) {u v : Word n}
    (h : Figure9Derives g u v) : eraseScalar u = u ↔ eraseScalar v = v := by
  induction h with
  | refl w => rfl
  | rule h => exact iff_of_true h.2.2.2.1 h.2.2.2.2
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | context l r h ih => simp only [eraseScalar_append_eq_self_iff, ih]

/-- No scalar-deletion rule is concealed in the source presentation. -/
theorem not_figure9Derives_scalar_nil (g : (ZMod d)ˣ) :
    ¬ Figure9Derives (n := n) g [.scalar] [] := by
  intro h
  have he := (h.eraseScalar_iff g).mpr rfl
  simp at he

end QuditClifford.Circuit
