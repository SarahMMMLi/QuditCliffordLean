import QuditClifford.Figure9Presented
import QuditClifford.AdjacentNormalCircuit

/-!
# Pauli erasure derived from the literal Figure 9 equations

The finite multiplier-power relation and C4 imply that the half-cycle
multiplier commutes with S. C2 identifies this multiplier with H squared.
Consequently the expanded Z and X words are identities, without adding
Pauli-erasure relations to the presentation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
set_option linter.unusedSectionVars false
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev fh (i : Fin n) : Figure9Presented g n :=
  figure9ClassWord g [.H i] (by simp)
private abbrev fs (i : Fin n) : Figure9Presented g n :=
  figure9ClassWord g [.S i] (by simp)
private abbrev fe (i : Fin n) (a : ZMod d) : Figure9Presented g n :=
  figure9ClassWord g (Sexp i a) (by simp)
private abbrev fm (i : Fin n) (a : (ZMod d)ˣ) : Figure9Presented g n :=
  figure9ClassWord g (multiplier i a) (by simp)

private theorem fe_pow (i : Fin n) (a : ZMod d) : fe g i a = fs g i ^ a.val :=
  figure9ClassWord_replicate g (.S i) (Gate.isAdjacent_S i) a.val

/-- C1 makes the residue-valued S exponent additive in the literal quotient. -/
theorem figure9ClassWord_Sexp_add (i : Fin n) (a b : ZMod d) :
    fe g i (a+b) = fe g i a * fe g i b := by
  have hs : fs g i ^ d = 1 := by
    have hr : Figure9Derives g (List.replicate d (.S i)) [] := by
      exact figure9Derives_rule (Figure9Rule.C1 i)
        (IsAdjacentWord.replicate (Gate.isAdjacent_S i) d) isAdjacentWord_nil
    have hc := (figure9ClassWord_eq_iff_derives g
      (List.replicate d (.S i)) []
      (IsAdjacentWord.replicate (Gate.isAdjacent_S i) d) isAdjacentWord_nil).mpr (by simpa using hr)
    rw [figure9ClassWord_replicate g (.S i) (Gate.isAdjacent_S i) d] at hc
    exact hc
  simp only [fe_pow, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod (a.val+b.val) hs).symm

@[simp] theorem figure9ClassWord_Sexp_zero (i : Fin n) : fe g i 0 = 1 := by
  simp [fe, Sexp]

@[simp] theorem figure9ClassWord_Sexp_one (i : Fin n) : fe g i 1 = fs g i := by
  simp [fe, fs, Sexp, ZMod.val_one]

/-- Multiplication of a field exponent is repeated S composition. -/
theorem figure9ClassWord_Sexp_nsmul (i : Fin n) (a : ZMod d) (k : ℕ) :
    fe g i ((k : ZMod d)*a) = fe g i a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      figure9ClassWord_Sexp_add, ih, pow_succ]

/-- C4 transports S through the multiplier generator. -/
theorem figure9ClassWord_multiplier_g_S (i : Fin n) :
    fm g i g * fs g i = fe g i ((↑g⁻¹ : ZMod d)^2) * fm g i g := by
  have hr : Figure9Derives g
      (eraseScalar (multiplier i g) ++ [.S i])
      (Sexp i ((↑g⁻¹ : ZMod d)^2) ++ eraseScalar (multiplier i g)) := by
    apply figure9Derives_rule (Figure9Rule.C4 i)
    · exact (isAdjacentWord_append _ _).mpr
        ⟨(isAdjacentWord_multiplier i g).eraseScalar, by simp⟩
    · exact (isAdjacentWord_append _ _).mpr
        ⟨isAdjacentWord_Sexp _ _, (isAdjacentWord_multiplier i g).eraseScalar⟩
  have hc := (figure9ClassWord_eq_iff_derives g
    (multiplier i g ++ [.S i])
    (Sexp i ((↑g⁻¹ : ZMod d)^2) ++ multiplier i g)
    ((isAdjacentWord_append _ _).mpr ⟨isAdjacentWord_multiplier i g, by simp⟩)
    ((isAdjacentWord_append _ _).mpr ⟨isAdjacentWord_Sexp _ _, isAdjacentWord_multiplier i g⟩)).mpr
      (by simpa only [eraseScalar_append, eraseScalar_S_cons, eraseScalar_nil,
        eraseScalar_Sexp] using hr)
  simpa only [figure9ClassWord_append, fe, fm, fs] using hc

/-- C4 transports every residue-valued S power. -/
theorem figure9ClassWord_multiplier_g_Sexp (i : Fin n) (a : ZMod d) :
    fm g i g * fe g i a = fe g i (a * (↑g⁻¹ : ZMod d)^2) * fm g i g := by
  have h := SemiconjBy.pow_right (figure9ClassWord_multiplier_g_S g i) a.val
  change fm g i g * fs g i ^ a.val =
    fe g i ((↑g⁻¹ : ZMod d)^2)^a.val * fm g i g at h
  rw [← figure9ClassWord_Sexp_nsmul, ZMod.natCast_zmod_val] at h
  simpa only [fe_pow] using h

/-- Iteration of C4 uses only the generator, without any all-unit assumption. -/
theorem figure9ClassWord_multiplier_gpow_Sexp (i : Fin n) (k : ℕ) (a : ZMod d) :
    fm g i g ^ k * fe g i a =
      fe g i (a * (↑g⁻¹ : ZMod d)^(2*k)) * fm g i g ^ k := by
  induction k generalizing a with
  | zero => simp only [pow_zero, one_mul, mul_one, zero_mul, mul_zero, pow_zero, mul_one]
  | succ k ih =>
    rw [pow_succ, mul_assoc, figure9ClassWord_multiplier_g_Sexp, ← mul_assoc, ih]
    have he : (a * (↑g⁻¹ : ZMod d)^2) * (↑g⁻¹ : ZMod d)^(2*k) =
        a * (↑g⁻¹ : ZMod d)^(2*(k+1)) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [he, mul_assoc, ← pow_succ]

/-- The primitive Fourier class has order four by C2 and finite C3. -/
theorem figure9ClassWord_H_four (i : Fin n) : fh g i ^ 4 = 1 := by
  have h := (figure9ClassWord_eq_iff_derives g
    (List.replicate 4 (.H i)) [] (by simp) (by simp)).mpr
    (by simpa using figure9Derives_H_four Fact.out g Fact.out i)
  simpa only [figure9ClassWord_replicate, figure9ClassWord_nil, fh] using h

/-- C2 identifies H squared with the expanded negation multiplier. -/
theorem figure9ClassWord_H_sq (i : Fin n) : fh g i ^ 2 = fm g i (-1) := by
  have h : Figure9Derives g [.H i,.H i]
      (eraseScalar (multiplier (d := d) i (-1))) := by
    exact figure9Derives_rule (Figure9Rule.C2 i) (by simp)
      (isAdjacentWord_multiplier i (-1 : (ZMod d)ˣ)).eraseScalar
  have hc := (figure9ClassWord_eq_iff_derives g
    [.H i,.H i] (multiplier i (-1)) (by simp) (isAdjacentWord_multiplier i _)).mpr (by simpa using h)
  change fh g i * fh g i = fm g i (-1) at hc
  simpa only [pow_two] using hc

/-- The generator midpoint is the negation multiplier by the finite C3 family. -/
theorem figure9ClassWord_multiplier_half (i : Fin n) :
    fm g i g ^ ((d-1)/2) = fm g i (-1) := by
  have hlt : (d-1)/2 < d := by have hp := NeZero.pos d; omega
  have h := figure9Derives_multiplier_generator_pow g i ⟨(d-1)/2,hlt⟩
  change Figure9Derives g (power (eraseScalar (multiplier i g)) ((d-1)/2))
    (eraseScalar (multiplier i (g^((d-1)/2)))) at h
  rw [generator_half_pow (Fact.out : Odd d) g Fact.out] at h
  have hc := (figure9ClassWord_eq_iff_derives g
    (power (multiplier i g) ((d-1)/2)) (multiplier i (-1))
    ((isAdjacentWord_multiplier i g).power _) (isAdjacentWord_multiplier i _)).mpr
      (by simpa only [eraseScalar_power] using h)
  rw [figure9ClassWord_power] at hc
  exact hc

/-- C4 iterated halfway around the generator cycle makes H squared commute with S. -/
theorem figure9ClassWord_H_sq_commute_S (i : Fin n) : Commute (fh g i ^ 2) (fs g i) := by
  have hp : (↑g⁻¹ : ZMod d)^(2*((d-1)/2)) = 1 := by
    have hhalf : 2*((d-1)/2) = d-1 := by
      have ho := Nat.odd_iff.mp (Fact.out : Odd d)
      omega
    rw [hhalf, ← Units.val_pow_eq_pow_val, inv_pow,
      ← (Fact.out : orderOf g = d-1), pow_orderOf_eq_one]
    simp
  have h := figure9ClassWord_multiplier_gpow_Sexp g i ((d-1)/2) 1
  rw [hp, one_mul, figure9ClassWord_Sexp_one, figure9ClassWord_multiplier_half,
    ← figure9ClassWord_H_sq] at h
  exact h

/-- The expanded Z word is erased by the eighteen Figure 9 rules themselves. -/
@[simp] theorem figure9ClassWord_Z (i : Fin n) :
    figure9ClassWord g (Z (d := d) i) (by simp) = 1 := by
  have hs : fs g i * fe g i (-1) = 1 := by
    rw [← figure9ClassWord_Sexp_one, ← figure9ClassWord_Sexp_add]
    simp
  have hcomm := (figure9ClassWord_H_sq_commute_S g i).eq
  have hz : figure9ClassWord g (Z (d := d) i) (by simp) =
      fh g i ^ 2 * fs g i * fh g i ^ 2 * fe g i (-1) := by
    change (fh g i * fh g i * fs g i * fh g i * fh g i) * fe g i (-1) = _
    simp only [pow_two, mul_assoc]
  rw [hz, hcomm]
  calc
    _ = fs g i * (fh g i ^ 2 * fh g i ^ 2) * fe g i (-1) := by group
    _ = fs g i * fe g i (-1) := by
      rw [← pow_add]
      norm_num only
      rw [figure9ClassWord_H_four, mul_one]
    _ = 1 := hs

/-- The expanded X word is erased without an additional Pauli rule. -/
@[simp] theorem figure9ClassWord_X (i : Fin n) :
    figure9ClassWord g (X (d := d) i) (by simp) = 1 := by
  have hz := figure9ClassWord_Z g i
  have hx : figure9ClassWord g (X (d := d) i) (by simp) =
      (fh g i)⁻¹ * figure9ClassWord g (Z (d := d) i) (by simp) * fh g i := by
    change (fh g i * fs g i * fh g i * fh g i) * fe g i (-1) * fh g i =
      (fh g i)⁻¹ * ((fh g i * fh g i * fs g i * fh g i * fh g i) * fe g i (-1)) * fh g i
    group
  rw [hx, hz]
  group

/-- Figure 9 derives the expanded Z deletion as a contextual rewrite. -/
theorem figure9Derives_Z (i : Fin n) : Figure9Derives g (Z (d := d) i) [] := by
  have h := (figure9ClassWord_eq_iff_derives g
    (Z (d := d) i) [] (by simp) (by simp)).mp (by simp)
  simpa using h

/-- Figure 9 derives the expanded X deletion as a contextual rewrite. -/
theorem figure9Derives_X (i : Fin n) : Figure9Derives g (X (d := d) i) [] := by
  have h := (figure9ClassWord_eq_iff_derives g
    (X (d := d) i) [] (by simp) (by simp)).mp (by simp)
  simpa using h

@[simp] theorem figure9ClassWord_Xexp (i : Fin n) (a : ZMod d) :
    figure9ClassWord g (Xexp i a) (by simp) = 1 := by
  simp [Xexp]

@[simp] theorem figure9ClassWord_Zexp (i : Fin n) (a : ZMod d) :
    figure9ClassWord g (Zexp i a) (by simp) = 1 := by
  simp [Zexp]

/-- Every residue-valued power of the expanded X word is derivably empty. -/
theorem figure9Derives_Xexp (i : Fin n) (a : ZMod d) :
    Figure9Derives g (Xexp i a) [] := by
  simpa [Xexp, power] using figure9Derives_power g (figure9Derives_X g i) a.val

/-- Every residue-valued power of the expanded Z word is derivably empty. -/
theorem figure9Derives_Zexp (i : Fin n) (a : ZMod d) :
    Figure9Derives g (Zexp i a) [] := by
  simpa [Zexp, power] using figure9Derives_power g (figure9Derives_Z g i) a.val

end QuditClifford.Circuit
