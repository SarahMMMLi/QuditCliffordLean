import QuditClifford.NormalCoordinates
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the paper's concrete normal layers

These are counts of the intrinsic A/B and D/E grammars, proved by bijections
with their label-read input spaces. They are independent of rewriting claims.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
universe u
variable {K : Type u} [Field K]

/-- Z-normal syntax is in bijection with the nonzero Pauli exponent vectors. -/
def ZNormal.equivNonzero (n : ℕ) :
    ZNormal K (n + 1) ≃ {v : Wires K (n + 1) // v ≠ 0} :=
  Equiv.ofBijective (fun N => ⟨N.input, N.input_ne_zero⟩) (by
    constructor
    · intro N M h
      exact input_injective (congrArg Subtype.val h)
    · intro v
      obtain ⟨N, hN⟩ := exists_input v.val v.property
      exact ⟨N, Subtype.ext hN⟩)

/-- X-normal syntax has one free E label and two labels per D box. -/
def XNormal.equivLabels (n : ℕ) : XNormal K (n + 1) ≃ (K × Wires K n) :=
  Equiv.ofBijective (fun N => (N.phase, Fin.tail N.input)) (by
    constructor
    · intro N M h
      apply input_injective
      apply ZNormal.wires_ext
      · rw [N.input_head, M.input_head]
        have hp : N.phase = M.phase := congrArg (fun x : K × Wires K n => x.1) h
        rw [hp]
      · exact congrArg Prod.snd h
    · rintro ⟨c, v⟩
      obtain ⟨N, hN⟩ := exists_input (Fin.cons (c, 1) v) rfl
      refine ⟨N, Prod.ext ?_ ?_⟩
      · have hh := congrArg (fun w : Wires K (n + 1) => (w 0).1) hN
        simpa only [N.input_head, Fin.cons_zero] using hh
      · simpa only [Fin.tail_cons] using congrArg Fin.tail hN)

variable [Fintype K]

/-- The number of Z-normal layers on n+1 wires. -/
theorem ZNormal.card (n : ℕ) :
    Nat.card (ZNormal K (n + 1)) = (Fintype.card K) ^ (2*(n+1)) - 1 := by
  classical
  rw [Nat.card_congr (ZNormal.equivNonzero n)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp [Wires, Vector, Fintype.card_fun, ← pow_two, ← pow_mul]

/-- The number of X-normal layers on n+1 wires. -/
theorem XNormal.card (n : ℕ) :
    Nat.card (XNormal K (n + 1)) = (Fintype.card K) ^ (2*n+1) := by
  rw [Nat.card_congr (XNormal.equivLabels n)]
  simp [Nat.card_eq_fintype_card, Wires, Vector, Fintype.card_fun,
    pow_add, pow_mul, pow_two, mul_comm, mul_pow]

/-- Counting the actual paired layers used by the recursive normal form. -/
theorem normalPair_card (n : ℕ) :
    Nat.card (ZNormal K (n + 1) × XNormal K (n + 1)) =
      ((Fintype.card K) ^ (2*(n+1)) - 1) * (Fintype.card K) ^ (2*n+1) := by
  rw [Nat.card_prod, ZNormal.card, XNormal.card]

end QuditClifford.NormalBoxes
