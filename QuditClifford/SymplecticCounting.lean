import QuditClifford.SymplecticNormalForm
import QuditClifford.NormalCounting
import QuditClifford.SymplecticCoordinates
import QuditClifford.PauliExactSequence

/-!
# Symplectic cardinality from the concrete recursive normal form

The counting argument uses the actual A/B/D/E syntax, its proved unique action,
and the explicit coordinate equivalence with the existing symplectic group.
It does not count the generated exact Clifford group or assume its quotient.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
universe u
variable {K : Type u} [Field K]

namespace SymplecticNormalForm

/-- The zero-wire grammar consists of the empty word. -/
def zeroEquiv : SymplecticNormalForm K 0 ≃ Unit where
  toFun _ := ()
  invFun _ := .empty
  left_inv N := by cases N; rfl
  right_inv x := by cases x; rfl

/-- The actual nonempty syntax has one pair of sweeps and a smaller normal word. -/
def stepEquiv (n : ℕ) : SymplecticNormalForm K (n + 1) ≃
    ZNormal K (n + 1) × (XNormal K (n + 1) × SymplecticNormalForm K n) where
  toFun N := match N with | .step Z X M => (Z, X, M)
  invFun x := .step x.1 x.2.1 x.2.2
  left_inv N := by cases N; rfl
  right_inv x := by cases x with | mk Z x => cases x; rfl

variable [Fintype K]

/-- Direct constructor count: no symplectic-group cardinality is assumed. -/
theorem card_succ (n : ℕ) :
    Nat.card (SymplecticNormalForm K (n + 1)) =
      ((Fintype.card K) ^ (2*(n+1)) - 1) *
        ((Fintype.card K) ^ (2*n+1) * Nat.card (SymplecticNormalForm K n)) := by
  rw [Nat.card_congr (stepEquiv n), Nat.card_prod, Nat.card_prod,
    ZNormal.card, XNormal.card]

/-- The cardinality of the actual recursive normal syntax. -/
theorem card (n : ℕ) :
    Nat.card (SymplecticNormalForm K n) =
      (Fintype.card K) ^ (n^2) * ∏ i ∈ Finset.range n, ((Fintype.card K) ^ (2*(i+1)) - 1) := by
  induction n with
  | zero =>
    rw [Nat.card_congr zeroEquiv]
    simp
  | succ n ih =>
    rw [card_succ, ih, Finset.prod_range_succ]
    have he : (n+1)^2 = (2*n+1) + n^2 := by ring
    rw [he, pow_add]
    ring

end SymplecticNormalForm

/-- Lemma 3.9 in wirewise coordinates, derived from Proposition 3.8's actual grammar. -/
theorem wireSymplectic_card [Fintype K] (n : ℕ) :
    Nat.card (WireSymplectic (K := K) n) =
      (Fintype.card K) ^ (n^2) * ∏ i ∈ Finset.range n, ((Fintype.card K) ^ (2*(i+1)) - 1) := by
  rw [← Nat.card_congr (SymplecticNormalForm.equivWireSymplectic n)]
  exact SymplecticNormalForm.card n

/-- Lemma 3.9 for the existing group acting on Pauli exponents. -/
theorem symplecticGroup_card (d n : ℕ) [Fact d.Prime] :
    Nat.card (symplecticGroup d n) =
      d ^ (n^2) * ∏ i ∈ Finset.range n, (d ^ (2*(i+1)) - 1) := by
  rw [← Nat.card_congr (wireSymplecticEquiv (d := d) (n := n)), wireSymplectic_card]
  simp only [ZMod.card]

/-- A consequent count for abstract scalar-fixing Pauli automorphisms. This
is not yet a count of the paper's generated exact Clifford matrix group. -/
theorem scalarFixingAut_card (d n : ℕ) [Fact d.Prime] (hd : Odd d) :
    Nat.card (Pauli.scalarFixingAut d n) =
      d ^ (n^2+2*n) * ∏ i ∈ Finset.range n, (d ^ (2*(i+1)) - 1) := by
  rw [Nat.card_congr (Pauli.autEquivCoordinates hd), Nat.card_prod]
  have hc : Nat.card (Multiplicative (PhaseSpace d n)) = d ^ (2*n) := by
    simp [Nat.card_eq_fintype_card, PhaseSpace, Fintype.card_fun, ← pow_two, ← pow_mul, Nat.mul_comm]
  rw [hc, symplecticGroup_card, pow_add]
  ring

end QuditClifford.NormalBoxes
