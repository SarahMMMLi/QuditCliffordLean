import QuditClifford.ControlledXPauliRewrites
import QuditClifford.WireRewrites

/-!
# Exact three-wire controlled-phase rewrites

C15 and its Fourier-square conjugate force the remote controlled phase to
commute with the adjacent controlled phase. This discharges a three-wire
commutation obligation syntactically, keeping the exact expanded CIZ word.
-/
noncomputable section
namespace QuditClifford.Circuit

private theorem commute_of_forward_and_inverse {G : Type*} [Group G]
    (q r x : G) (he : q*x = r*x*q) (hi : q⁻¹*x = r⁻¹*x*q⁻¹) : Commute q r := by
  have ht : x*q = q*r⁻¹*x := by
    calc
      x*q = q*(q⁻¹*x)*q := by group
      _ = q*(r⁻¹*x*q⁻¹)*q := by rw [hi]
      _ = q*r⁻¹*x := by group
  have hq : q = r*q*r⁻¹ := by
    apply mul_right_cancel (b := x)
    calc
      q*x = r*(x*q) := by simpa only [mul_assoc] using he
      _ = r*(q*r⁻¹*x) := by rw [ht]
      _ = (r*q*r⁻¹)*x := by group
  show q*r = r*q
  calc
    q*r = (r*q*r⁻¹)*r := congrArg (fun z => z*r) hq
    _ = r*q := by group

private theorem conjugate_of_transport {G : Type*} [Group G]
    (h t a c : G) (ht : h*t = t*a) (hc : a*c*a⁻¹ = c⁻¹) :
    h*(t*c*t⁻¹)*h⁻¹ = (t*c*t⁻¹)⁻¹ := by
  calc
    h*(t*c*t⁻¹)*h⁻¹ = (h*t)*c*(h*t)⁻¹ := by group
    _ = (t*a)*c*(t*a)⁻¹ := by rw [ht]
    _ = t*(a*c*a⁻¹)*t⁻¹ := by group
    _ = (t*c*t⁻¹)⁻¹ := by rw [hc]; group

variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

set_option linter.unusedSectionVars false in
omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem primitive_disjoint (a b : Gate n) (hab : Disjoint a.support b.support) :
    Commute (classWord g [a]) (classWord g [b]) :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inl (.disjoint a b hab)))

/-- The literal remote-CZ macro is a conjugate by the exact SWAP word. -/
theorem classWord_CIZ_conjugate (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    classWord g (CIZ (d := d) i j k hij hjk hik) =
      classWord g (SWAP (d := d) j k hjk) * classWord g [.CZ i j hij] *
        (classWord g (SWAP (d := d) j k hjk))⁻¹ := by
  have ht : classWord g (SWAP (d := d) j k hjk) *
      classWord g (SWAP (d := d) j k hjk) = 1 :=
    (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (.C7 j k hjk)))
  have hi := inv_eq_of_mul_eq_one_right ht
  simp only [CIZ, classWord_append, hi]

/-- Fourier-square inversion at the remote endpoint is derived through SWAP. -/
theorem classWord_H_sq_conjugate_CIZ_last (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (classWord g [.H k])^2 * classWord g (CIZ (d := d) i j k hij hjk hik) *
      ((classWord g [.H k])^2)⁻¹ =
        (classWord g (CIZ (d := d) i j k hij hjk hik))⁻¹ := by
  have ht := ((classWord_semiconj_iff g _ _ _).mpr (derives_SWAP_H_left g j k hjk)).pow_right 2
  rw [classWord_CIZ_conjugate]
  exact conjugate_of_transport _ _ _ _ ht.symm (classWord_H_sq_conjugate_CZ_right g i j hij)

set_option linter.unusedSectionVars false in
omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- C15 in the exact syntactic group. -/
theorem classWord_CZ_CX_overlap (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    classWord g [.CZ j k hjk] * classWord g (CX i j hij) =
      classWord g (CIZ (d := d) i j k hij hjk hik) *
        classWord g (CX i j hij) * classWord g [.CZ j k hjk] :=
  (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (.C15 i j k hij hjk hik)))

/-- The adjacent and remote controlled phases commute by C15 and its
Fourier-square conjugate, rather than by backwards use of matrix equality. -/
theorem classWord_CZ_commute_CIZ (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Commute (classWord g [.CZ j k hjk]) (classWord g (CIZ (d := d) i j k hij hjk hik)) := by
  let F := MulAut.conj ((classWord g [.H k])^2)
  have hh := primitive_disjoint g (.H k) (.H j) (by simp [Gate.support, hjk, hjk.symm])
  have hc := primitive_disjoint g (.H k) (.CZ i j hij)
    (by simp [Gate.support, hik, hik.symm, hjk, hjk.symm])
  have hx : Commute ((classWord g [.H k])^2) (classWord g (CX i j hij)) := by
    have he := ((((hh.mul_right hh).mul_right hh).mul_right hc).mul_right hh).pow_left 2
    exact he
  have hFx : F (classWord g (CX i j hij)) = classWord g (CX i j hij) := by
    change (classWord g [.H k])^2 * classWord g (CX i j hij) * ((classWord g [.H k])^2)⁻¹ = _
    rw [hx.eq]
    group
  have hFq : F (classWord g [.CZ j k hjk]) = (classWord g [.CZ j k hjk])⁻¹ :=
    classWord_H_sq_conjugate_CZ_right g j k hjk
  have hFr : F (classWord g (CIZ (d := d) i j k hij hjk hik)) =
      (classWord g (CIZ (d := d) i j k hij hjk hik))⁻¹ :=
    classWord_H_sq_conjugate_CIZ_last g i j k hij hjk hik
  have hi := congrArg F (classWord_CZ_CX_overlap g i j k hij hjk hik)
  simp only [map_mul, hFq, hFr, hFx] at hi
  exact commute_of_forward_and_inverse _ _ _
    (classWord_CZ_CX_overlap g i j k hij hjk hik) hi

/-- The reverse transport has the inverse remote phase, with no scalar loss. -/
theorem classWord_CX_CZ_overlap (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    classWord g (CX i j hij) * classWord g [.CZ j k hjk] =
      classWord g [.CZ j k hjk] *
        (classWord g (CIZ (d := d) i j k hij hjk hik))⁻¹ * classWord g (CX i j hij) := by
  have hr := classWord_CZ_CX_overlap g i j k hij hjk hik
  have hc := (classWord_CZ_commute_CIZ g i j k hij hjk hik).inv_right
  calc
    _ = (classWord g (CIZ (d := d) i j k hij hjk hik))⁻¹ *
      (classWord g [.CZ j k hjk] * classWord g (CX i j hij)) := by rw [hr]; group
    _ = _ := by rw [← mul_assoc, hc.eq]

end QuditClifford.Circuit
