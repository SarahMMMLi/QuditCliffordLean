import QuditClifford.SymplecticTwoWireB
import QuditClifford.ThreeWireControlledRewrites

/-! # Exact controlled-phase commutation and SWAP transport -/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Adjacent controlled phases commute as a consequence of C15 and SWAP,
using the already derived adjacent/remote commutation law. -/
theorem classWord_CZ_commute_overlap (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Commute (classWord g [.CZ j k hjk]) (classWord g [.CZ i j hij]) := by
  have hc := classWord_CZ_commute_CIZ g i j k hij hjk hik
  rw [classWord_CIZ_conjugate] at hc
  have ht := (classWord_SWAP_commute_CZ g j k hjk).symm
  have he := (ht.inv_right.mul_right hc).mul_right ht
  have hh : (classWord g (SWAP (d := d) j k hjk))⁻¹ *
      (classWord g (SWAP (d := d) j k hjk) * classWord g [.CZ i j hij] *
        (classWord g (SWAP (d := d) j k hjk))⁻¹) * classWord g (SWAP (d := d) j k hjk) =
      classWord g [.CZ i j hij] := by group
  rw [hh] at he
  exact he

set_option linter.unusedSectionVars false in
/-- C14 is the exact two-SWAP transport of an adjacent controlled phase. -/
theorem classWord_SWAP_SWAP_CZ (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    classWord g (SWAP (d := d) j k hjk) * classWord g (SWAP (d := d) i j hij) *
        classWord g [.CZ j k hjk] =
      classWord g [.CZ i j hij] * classWord g (SWAP (d := d) j k hjk) *
        classWord g (SWAP (d := d) i j hij) :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (.C14 i j k hij hjk hik)))

end QuditClifford.Circuit
