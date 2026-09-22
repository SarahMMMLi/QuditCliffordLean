import QuditClifford.ThreeWirePhaseTransport
import QuditClifford.RelabelRewrites

/-!
# The two three-wire B/CZ box cases

All calculations below take place in the exact Figure 1 quotient. C14 gives
the two equivalent SWAP realizations of the remote controlled phase; C15
then extends to every controlled-addition power by syntactic commutation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- C14 identifies the two adjacent-SWAP expansions of a remote controlled phase. -/
theorem classWord_CIZ_other_conjugate (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    classWord g (CIZ (d := d) i j k hij hjk hik) =
      classWord g (SWAP (d := d) i j hij) * classWord g [.CZ j k hjk] *
        (classWord g (SWAP (d := d) i j hij))⁻¹ := by
  let T := classWord g (SWAP (d := d) j k hjk)
  let W := classWord g (SWAP (d := d) i j hij)
  let C := classWord g [.CZ i j hij]
  let Q := classWord g [.CZ j k hjk]
  have ht : T*T = 1 := classWord_SWAP_sq g j k hjk
  have hc : T*W*Q = C*T*W := classWord_SWAP_SWAP_CZ g i j k hij hjk hik
  rw [classWord_CIZ_conjugate]
  change T*C*T⁻¹ = W*Q*W⁻¹
  calc
    _ = T*C*T := by rw [inv_eq_of_mul_eq_one_right ht]
    _ = T*(C*T*W)*W⁻¹ := by group
    _ = T*(T*W*Q)*W⁻¹ := by rw [← hc]
    _ = (T*T)*(W*Q*W⁻¹) := by group
    _ = _ := by rw [ht, one_mul]

/-- The remote controlled phase commutes with the first adjacent phase too. -/
theorem classWord_CZ_first_commute_CIZ (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Commute (classWord g [.CZ i j hij]) (classWord g (CIZ (d := d) i j k hij hjk hik)) := by
  rw [classWord_CIZ_other_conjugate]
  have hW := (classWord_SWAP_commute_CZ g i j hij).symm
  exact (hW.mul_right (classWord_CZ_commute_overlap g i j k hij hjk hik).symm).mul_right hW.inv_right

/-- H on the intermediate wire commutes with the remote controlled phase. -/
theorem classWord_H_middle_commute_CIZ (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Commute (classWord g [.H j]) (classWord g (CIZ (d := d) i j k hij hjk hik)) := by
  let T := classWord g (SWAP (d := d) j k hjk)
  have hc := classWord_disjoint g (.H k) (.CZ i j hij)
    (by simp [Gate.support, hik, hjk])
  have hh : T*classWord g [.H k]*T⁻¹ = classWord g [.H j] := by
    rw [show T*classWord g [.H k] = classWord g [.H j]*T from classWord_SWAP_H_right g j k hjk]
    group
  have hm := congrArg (MulAut.conj T) hc.eq
  simp only [map_mul] at hm
  change Commute _ _
  rw [classWord_CIZ_conjugate, ← hh]
  exact hm

/-- C15's correcting remote phase commutes with the controlled addition. -/
theorem classWord_CX_commute_CIZ (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Commute (classWord g (CX i j hij)) (classWord g (CIZ (d := d) i j k hij hjk hik)) := by
  rw [classWord_CX_conjugate]
  have hh := classWord_H_middle_commute_CIZ g i j k hij hjk hik
  exact (hh.inv_left.mul_left (classWord_CZ_first_commute_CIZ g i j k hij hjk hik)).mul_left hh

private theorem pow_overlap {G : Type*} [Group G] (x q r : G)
    (hx : x*q = q*r⁻¹*x) (hr : Commute x r) (k : ℕ) :
    x^k*q = q*(r⁻¹)^k*x^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = x^k*(x*q) := by rw [pow_succ, mul_assoc]
      _ = x^k*(q*r⁻¹*x) := by rw [hx]
      _ = (x^k*q)*r⁻¹*x := by group
      _ = q*(r⁻¹)^k*(x^k*r⁻¹)*x := by rw [ih]; group
      _ = q*(r⁻¹)^k*(r⁻¹*x^k)*x := by rw [(hr.pow_left k).inv_right.eq]
      _ = _ := by rw [pow_succ, pow_succ]; group

/-- C15 extends to all natural powers, with the exact inverse remote phase. -/
theorem classWord_CXpow_CZ_overlap (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : ℕ) :
    classWord g (CX i j hij)^a * classWord g [.CZ j k hjk] =
      classWord g [.CZ j k hjk] *
        ((classWord g (CIZ (d := d) i j k hij hjk hik))⁻¹)^a * classWord g (CX i j hij)^a :=
  pow_overlap _ _ _ (classWord_CX_CZ_overlap g i j k hij hjk hik)
    (classWord_CX_commute_CIZ g i j k hij hjk hik) a

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The zero-a B/CZ case, including the zero-b subcase, holds exactly. -/
theorem derives_B_CZ_lower_zero (b : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (bWord 0 b i j hij ++ [.CZ j k hjk])
      (Circuit.CIZ (d := d) i j k hij hjk hik ++ List.replicate (-b).val (.CZ j k hjk) ++
        bWord 0 b i j hij) := by
  let T := classWord g (Circuit.SWAP (d := d) i j hij)
  let X := classWord g (Circuit.CX i j hij)
  let Q := classWord g [.CZ j k hjk]
  let R := classWord g (Circuit.CIZ (d := d) i j k hij hjk hik)
  have hT : T*T = 1 := classWord_SWAP_sq g i j hij
  have hR : R = T*Q*T⁻¹ := classWord_CIZ_other_conjugate g i j k hij hjk hik
  have hTQ : T*Q = R*T := by rw [hR]; group
  have hTR : T*R = Q*T := by
    rw [hR, inv_eq_of_mul_eq_one_right hT]
    calc
      T*(T*Q*T) = (T*T)*Q*T := by group
      _ = Q*T := by rw [hT, one_mul]
  have hpower : T*(R⁻¹)^b.val = (Q⁻¹)^b.val*T :=
    (show SemiconjBy T R Q from hTR).inv_right.pow_right b.val
  have hx : X^b.val*Q = Q*(R⁻¹)^b.val*X^b.val :=
    classWord_CXpow_CZ_overlap g i j k hij hjk hik b.val
  have hb : classWord g (List.replicate (-b).val (.CZ j k hjk)) = (Q⁻¹)^b.val := by
    rw [classWord_replicate, classWord_CZexp_neg, inv_pow]
  apply (classWord_eq_iff_derives g _ _).mp
  simp only [bWord, if_pos rfl, ite_true, classWord_append, classWord_power, hb]
  change (T*X^b.val)*Q = R*(Q⁻¹)^b.val*(T*X^b.val)
  calc
    _ = T*(Q*(R⁻¹)^b.val*X^b.val) := by rw [mul_assoc, hx]
    _ = (T*Q)*(R⁻¹)^b.val*X^b.val := by group
    _ = R*(T*(R⁻¹)^b.val)*X^b.val := by rw [hTQ]; group
    _ = _ := by rw [hpower]; group

/-- The nonzero-a B/CZ case retains the entire B word and emits two phases. -/
theorem derives_B_CZ_lower_nonzero (a b : ZMod d) (ha : a ≠ 0) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (bWord a b i j hij ++ [.CZ j k hjk])
      (Circuit.CIZ (d := d) i j k hij hjk hik ++ List.replicate (-a).val (.CZ j k hjk) ++
        bWord a b i j hij) := by
  have hbase := (classWord_eq_iff_derives g _ _).mpr
    (derives_B_CZ_lower_zero g a i j k hij hjk hik)
  have hH := classWord_disjoint g (.H i) (.CZ j k hjk)
    (by simp [Gate.support, hij, hik, hij.symm, hik.symm])
  have hS := (classWord_disjoint g (.S i) (.CZ j k hjk)
    (by simp [Gate.support, hij, hik, hij.symm, hik.symm])).pow_left (-b/a).val
  have hc : Commute (classWord g [.H i] * classWord g (Sexp i (-b/a)))
      (classWord g [.CZ j k hjk]) := by
    simpa only [Sexp, classWord_replicate] using hH.mul_left hS
  apply (classWord_eq_iff_derives g _ _).mp
  simp only [bWord, if_pos rfl, ite_true, classWord_append, classWord_power] at hbase
  simp only [bWord, if_neg ha, classWord_append, classWord_power]
  calc
    _ = (classWord g (Circuit.SWAP (d := d) i j hij)*classWord g (Circuit.CX i j hij)^a.val) *
        ((classWord g [.H i]*classWord g (Sexp i (-b/a)))*classWord g [.CZ j k hjk]) := by group
    _ = _ := by rw [hc.eq]; rw [← mul_assoc, hbase]; group

end QuditClifford.NormalBoxes
