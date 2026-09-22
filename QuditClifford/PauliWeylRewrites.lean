import QuditClifford.DerivedPauliRewrites

/-!
# Exact Weyl relations from the Figure 1 presentation

These proofs use the actual primitive-word quotient and its already derived
inverses. In particular no matrix equality is converted into a rewrite.
-/

noncomputable section
namespace QuditClifford.Circuit

variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev t : PresentedCircuit g n := classWord g [.scalar]
private abbrev h (i : Fin n) : PresentedCircuit g n := classWord g [.H i]
private abbrev s (i : Fin n) : PresentedCircuit g n := classWord g [.S i]
private abbrev z (i : Fin n) : PresentedCircuit g n := classWord g (Z (d := d) i)
private abbrev x (i : Fin n) : PresentedCircuit g n := classWord g (X (d := d) i)
private abbrev o (a : ZMod d) : PresentedCircuit g n := classWord g (omegaPower a)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem scalar_class (k : ℕ) : classWord g (scalar (n := n) k) = t g ^ k :=
  classWord_replicate g .scalar k

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem t_order : (t g : PresentedCircuit g n) ^ (2*d) = 1 := by
  have he := (classWord_eq_iff_derives g (scalar (n := n) (2*d)) []).mpr
    (.rule (Or.inr Figure1Rule.C0))
  simpa only [scalar_class, classWord_nil] using he

omit [Fact (orderOf g = d-1)] in
private theorem omega_order : ((t g : PresentedCircuit g n) ^ (d+1)) ^ d = 1 := by
  have hd := Nat.odd_iff.mp (show Odd d from Fact.out)
  have hdiv : 2*((d+1)/2) = d+1 := by omega
  have he : (d+1)*d = (2*d)*((d+1)/2) := by rw [mul_comm 2 d, mul_assoc, hdiv, mul_comm]
  rw [← pow_mul, he, pow_mul, t_order, one_pow]

omit [Fact (orderOf g = d-1)] in
/-- The displayed omega words add their residue exponents using C0. -/
theorem classWord_omegaPower_add (a b : ZMod d) :
    classWord g (omegaPower (n := n) (a+b)) =
      classWord g (omegaPower a) * classWord g (omegaPower b) := by
  simp only [omegaPower, scalar_class, pow_mul]
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod (a.val+b.val) (omega_order (n := n) g)).symm

set_option linter.unusedSectionVars false in
@[simp] theorem classWord_omegaPower_zero :
    classWord g (omegaPower (n := n) (0 : ZMod d)) = 1 := by
  simp [omegaPower, scalar]

/-- Negating a residue gives the group inverse of its exact omega word. -/
theorem classWord_omegaPower_neg (a : ZMod d) :
    classWord g (omegaPower (n := n) (-a)) = (classWord g (omegaPower a))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← classWord_omegaPower_add, neg_add_cancel, classWord_omegaPower_zero]

set_option linter.unusedSectionVars false in
/-- Every exact omega phase is central in the actual word quotient. -/
theorem classWord_omegaPower_commute (a : ZMod d) (q : PresentedCircuit g n) :
    Commute (classWord g (omegaPower a)) q := by
  obtain ⟨w, rfl⟩ := classWord_surjective g q
  have he := (classWord_eq_iff_derives g _ _).mpr
    (derives_scalar_commute g ((d+1)*a.val) w)
  simpa only [classWord_append, omegaPower] using he

private theorem h_four (i : Fin n) : h g i ^ 4 = 1 := by
  have he := (classWord_eq_iff_derives g (List.replicate 4 (.H i)) []).mpr
    (derives_H_four Fact.out g Fact.out i)
  simpa only [classWord_replicate, classWord_nil] using he

private theorem h_sq_inv (i : Fin n) : (h g i ^ 2)⁻¹ = h g i ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add]
  exact h_four g i

private theorem z_expand (i : Fin n) :
    z g i = h g i ^ 2 * s g i * h g i ^ 2 * (s g i)⁻¹ := by
  change (h g i * h g i * s g i * h g i * h g i) *
    classWord g (Sexp i (-1 : ZMod d)) = _
  rw [classWord_Sexp_neg_one]
  simp only [pow_two, mul_assoc, s]

private theorem x_expand (i : Fin n) :
    x g i = h g i * s g i * h g i ^ 2 * (s g i)⁻¹ * h g i := by
  change (h g i * s g i * h g i * h g i) *
    classWord g (Sexp i (-1 : ZMod d)) * h g i = _
  rw [classWord_Sexp_neg_one]
  simp only [pow_two, mul_assoc, s]

private theorem val_neg_one_pred : (-1 : ZMod d).val = d-1 := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => simpa only [Nat.add_sub_cancel] using ZMod.val_neg_one k

private theorem zexp_neg_one (i : Fin n) :
    classWord g (Zexp i (-1 : ZMod d)) = (z g i)⁻¹ := by
  rw [Zexp, classWord_power, val_neg_one_pred]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))]
  exact classWord_Z_order g i

omit [NeZero d] in
private theorem two_ne_zero : (2 : ZMod d) ≠ 0 := by
  intro he
  have hh := QuditClifford.two_mul_half d (show Odd d from Fact.out)
  simp [he] at hh

private theorem sign_cancel : Even ((d-1)/2 + legendreSign (-1 : (ZMod d)ˣ)) := by
  have he : (-1 : ℂ)^((d-1)/2) = (-1 : ℂ)^legendreSign (-1 : (ZMod d)ˣ) := by
    rw [← QuditClifford.lambda_sq d Fact.out,
      QuditClifford.lambda_sq_eq_complexQuadraticChar d Fact.out]
    exact QuditClifford.complexQuadraticChar_eq_sign d (-1)
  apply (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp
  rw [pow_add, he, ← pow_two, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

omit [Fact (orderOf g = d-1)] in
private theorem sign_words_cancel :
    classWord g (scalar (n := n) (d*((d-1)/2))) *
      classWord g (scalar (d*legendreSign (-1 : (ZMod d)ˣ))) = 1 := by
  obtain ⟨k, hk⟩ := sign_cancel (d := d)
  rw [scalar_class, scalar_class, ← pow_add, ← Nat.mul_add, hk]
  have he : d*(k+k) = (2*d)*k := by ring
  rw [he, pow_mul, t_order, one_pow]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem multiplier_one_class (i : Fin n) :
    classWord g (multiplier (d := d) i 1) = o g (8⁻¹ : ZMod d) * (s g i * h g i)^3 := by
  have hone : (1 : ZMod d).val = 1 := ZMod.val_one d
  simp only [multiplier, Units.val_one, inv_one, one_pow, mul_one, sub_self,
    zero_mul, legendreSign, IsSquare.one, ↓reduceIte, mul_zero, scalar,
    List.replicate_zero, List.nil_append, Zexp, Xexp, ZMod.val_zero, power_zero]
  have he : (-1+4-2 : ZMod d) = 1 := by ring
  simp only [he, one_mul, Sexp, hone, List.replicate_one, List.append_nil]
  change o g (8⁻¹ : ZMod d) * s g i * h g i * s g i * h g i * s g i * h g i = _
  simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc]

/-- The scalar-refined one-wire cubic relation follows directly from T1 and C3. -/
theorem classWord_SH_cube (i : Fin n) :
    (classWord g [.S i] * classWord g [.H i])^3 =
      classWord g (omegaPower (n := n) (-(8 : ZMod d)⁻¹)) := by
  have he := (classWord_eq_iff_derives g (multiplier (d := d) i 1) []).mpr
    (derives_multiplier_one g i)
  rw [multiplier_one_class, classWord_nil] at he
  rw [classWord_omegaPower_neg]
  exact eq_inv_of_mul_eq_one_right he

private theorem multiplier_neg_one_class (i : Fin n) :
    classWord g (multiplier (d := d) i (-1)) =
      classWord g (scalar (d*legendreSign (-1 : (ZMod d)ˣ))) *
      o g (7*(8 : ZMod d)⁻¹) * (z g i)⁻¹ * x g i * ((s g i)⁻¹ * h g i)^3 := by
  have hone : (1 : ZMod d).val = 1 := ZMod.val_one d
  have htwo := two_ne_zero (d := d)
  have heZ : (1-(-1 : ZMod d))*(2*(-1))⁻¹ = -1 := by
    norm_num only [sub_neg_eq_add, one_add_one_eq_two, mul_neg_one, inv_neg, mul_neg]
    rw [mul_inv_cancel₀ htwo]
  have heX : (1-(-1 : ZMod d))*(2 : ZMod d)⁻¹ = 1 := by field_simp; ring
  have heO : (-(-1 : ZMod d)^2+4*(-1)-2)*(8*(-1))⁻¹ = 7*(8 : ZMod d)⁻¹ := by
    simp only [mul_neg_one, inv_neg]; ring
  simp only [multiplier, Units.val_neg, Units.val_one, Units.val_inv_eq_inv_val,
    inv_neg, inv_one, heZ, heX, heO, classWord_append, zexp_neg_one,
    Xexp, classWord_power, hone, pow_one, classWord_Sexp_neg_one]
  change classWord g (scalar (d*legendreSign (-1 : (ZMod d)ˣ))) *
    o g (7*(8 : ZMod d)⁻¹) * (z g i)⁻¹ * x g i * (s g i)⁻¹ * h g i *
    (s g i)⁻¹ * h g i * (s g i)⁻¹ * h g i = _
  simp only [pow_succ, pow_zero, mul_one, one_mul, mul_assoc]

private theorem h_sq_from_multiplier (i : Fin n) :
    h g i ^ 2 = o g (7*(8 : ZMod d)⁻¹) * (z g i)⁻¹ * x g i * ((s g i)⁻¹*h g i)^3 := by
  have he := (classWord_eq_iff_derives g _ _).mpr
    (show Derives g [.H i,.H i]
      (scalar (d*((d-1)/2)) ++ multiplier (d := d) i (-1)) from
      .rule (Or.inr (Figure1Rule.C2 i)))
  rw [classWord_append, multiplier_neg_one_class] at he
  change h g i * h g i = _ at he
  simpa only [← mul_assoc, sign_words_cancel, one_mul, pow_two] using he

private theorem commutator_algebra (i : Fin n) :
    (x g i)⁻¹ * h g i ^ 2 * (((s g i)⁻¹*h g i)^3)⁻¹ * z g i =
      (h g i)⁻¹ * (s g i*h g i)^3 * h g i := by
  have hc : (h g i)⁻¹*(h g i)⁻¹*(h g i)⁻¹ = h g i := by
    apply (mul_left_cancel_iff (a := h g i)).mp
    have hh := h_four g i
    have hi : (h g i)⁻¹ = (h g i)^3 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', hh]
    rw [hi]
    simp only [← pow_succ', ← pow_add]
    change h g i ^ 10 = h g i ^ 2
    calc
      _ = h g i ^ 4 * h g i ^ 4 * h g i ^ 2 := by simp only [← pow_add]
      _ = _ := by rw [hh, one_mul, one_mul]
  calc
    _ = (h g i)⁻¹ * s g i * ((h g i)⁻¹*(h g i)⁻¹*(h g i)⁻¹) *
        s g i * (h g i)⁻¹ * (s g i * z g i) := by
          rw [x_expand]
          simp only [pow_succ, pow_zero, one_mul, mul_one]
          group
    _ = (h g i)⁻¹ * s g i * h g i * s g i * (h g i)⁻¹ * (z g i * s g i) := by
          rw [hc, (classWord_Z_commute_S g i).symm.eq]
    _ = _ := by
      rw [z_expand]
      simp only [pow_succ, pow_zero, one_mul, mul_one]
      group

private theorem inverse_commutator (i : Fin n) :
    (x g i)⁻¹ * (z g i)⁻¹ * x g i * z g i = o g (-1 : ZMod d) := by
  have hm := h_sq_from_multiplier g i
  have hz : (z g i)⁻¹*x g i =
      o g (-(7*(8 : ZMod d)⁻¹)) * h g i^2 * (((s g i)⁻¹*h g i)^3)⁻¹ := by
    have ho : o (n := n) g (-(7*(8 : ZMod d)⁻¹)) = (o g (7*(8 : ZMod d)⁻¹))⁻¹ :=
      classWord_omegaPower_neg g _
    rw [ho, hm]
    group
  calc
    _ = (x g i)⁻¹ * ((z g i)⁻¹*x g i) * z g i := by group
    _ = o g (-(7*(8 : ZMod d)⁻¹)) *
        ((x g i)⁻¹ * h g i ^ 2 * (((s g i)⁻¹*h g i)^3)⁻¹ * z g i) := by
      rw [hz]
      have hc := (classWord_omegaPower_commute g (-(7*(8 : ZMod d)⁻¹)) ((x g i)⁻¹)).symm.eq
      simp only [← mul_assoc]
      rw [hc]
    _ = o g (-(7*(8 : ZMod d)⁻¹)) * ((h g i)⁻¹ * (s g i*h g i)^3 * h g i) := by
      rw [commutator_algebra]
    _ = o g (-(7*(8 : ZMod d)⁻¹)) * o g (-(8 : ZMod d)⁻¹) := by
      rw [classWord_SH_cube]
      have hc := (classWord_omegaPower_commute g (-(8 : ZMod d)⁻¹) ((h g i)⁻¹)).symm.eq
      rw [hc]
      group
    _ = _ := by
      rw [← classWord_omegaPower_add]
      apply congrArg (fun a : ZMod d => o (n := n) g a)
      have h8 : (8 : ZMod d) ≠ 0 := by
        have ht := two_ne_zero (d := d)
        convert pow_ne_zero 3 ht using 1
        norm_num
      calc
        _ = -(8*(8 : ZMod d)⁻¹) := by ring
        _ = -1 := by rw [mul_inv_cancel₀ h8]

/-- Exact Weyl commutation is a consequence of the primitive Figure 1 rules. -/
theorem classWord_ZX (i : Fin n) :
    classWord g (Z (d := d) i) * classWord g (X (d := d) i) =
      classWord g (omegaPower (1 : ZMod d)) *
        classWord g (X (d := d) i) * classWord g (Z (d := d) i) := by
  have he := inverse_commutator g i
  have ho : o (n := n) g (-1 : ZMod d) = (o g (1 : ZMod d))⁻¹ :=
    classWord_omegaPower_neg g 1
  rw [ho] at he
  change z g i * x g i = o g 1 * x g i * z g i
  calc
    _ = z g i * x g i * ((o g 1)⁻¹ * o g 1) := by simp only [inv_mul_cancel, mul_one]
    _ = z g i * x g i * (((x g i)⁻¹*(z g i)⁻¹*x g i*z g i) * o g 1) := by rw [he]
    _ = x g i * z g i * o g 1 := by group
    _ = _ := by
      have hc := (classWord_omegaPower_commute g (1 : ZMod d) (x g i*z g i)).symm.eq
      simpa only [mul_assoc] using hc

/-- The other Fourier pushing identity, with the actual inverse X word. -/
theorem classWord_HZ (i : Fin n) :
    classWord g [.H i] * classWord g (Z (d := d) i) =
      (classWord g (X (d := d) i))⁻¹ * classWord g [.H i] := by
  change h g i * z g i = (x g i)⁻¹ * h g i
  rw [x_expand, z_expand]
  simp only [mul_inv_rev, inv_inv, h_sq_inv]
  have hh : h g i * h g i^2 = (h g i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ', ← pow_succ] using h_four g i
  simp only [mul_assoc]
  rw [← mul_assoc (h g i) (h g i^2), hh]
  group

/-- The phase-gate pushing identity is derived with its exact scalar cancellation. -/
theorem classWord_SX (i : Fin n) :
    classWord g [.S i] * classWord g (X (d := d) i) =
      classWord g (X (d := d) i) * classWord g (Z (d := d) i) * classWord g [.S i] := by
  let p : PresentedCircuit g n := h g i^2*s g i*h g i^2
  have hp : p = z g i*s g i := by rw [z_expand]; dsimp [p]; group
  have hpc : Commute (s g i) p := by
    rw [hp]
    exact (classWord_Z_commute_S g i).symm.mul_right (Commute.refl _)
  have hpi : p⁻¹ = h g i^2*(s g i)⁻¹*h g i^2 := by
    dsimp [p]
    simp only [mul_inv_rev, h_sq_inv, mul_assoc]
  have hh : h g i*h g i^2 = (h g i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ', ← pow_succ] using h_four g i
  have hsh : s g i*h g i*s g i*h g i =
      o g (-(8 : ZMod d)⁻¹) * (h g i)⁻¹*(s g i)⁻¹ := by
    have he := classWord_SH_cube g i
    change (s g i*h g i)^3 = o g (-(8 : ZMod d)⁻¹) at he
    calc
      _ = (s g i*h g i)^3 * (h g i)⁻¹*(s g i)⁻¹ := by
        simp only [pow_succ, pow_zero, mul_one, one_mul]
        group
      _ = _ := by rw [he]
  have hl : s g i*x g i = o g (-(8 : ZMod d)⁻¹)*
      ((h g i)⁻¹*(s g i)⁻¹*h g i*(s g i)⁻¹*h g i) := by
    rw [x_expand]
    calc
      _ = (s g i*h g i*s g i*h g i)*h g i*(s g i)⁻¹*h g i := by
        simp only [pow_two, mul_assoc]
      _ = _ := by rw [hsh]; group
  change s g i*x g i = x g i*z g i*s g i
  rw [hl]
  symm
  calc
    _ = x g i*p := by rw [hp]; group
    _ = h g i*s g i*p⁻¹*h g i*s g i*h g i^2 := by
      rw [x_expand, hpi]
      dsimp [p]
      group
    _ = h g i*p⁻¹*s g i*h g i*s g i*h g i^2 := by
      rw [mul_assoc (h g i) (s g i) p⁻¹, hpc.inv_right.eq, ← mul_assoc]
    _ = (h g i)⁻¹*(s g i)⁻¹*h g i^2*(s g i*h g i*s g i*h g i)*h g i := by
      rw [hpi]
      simp only [← mul_assoc]
      rw [hh]
      simp only [pow_two, mul_assoc]
    _ = (h g i)⁻¹*(s g i)⁻¹*h g i^2*
        (o g (-(8 : ZMod d)⁻¹)*(h g i)⁻¹*(s g i)⁻¹)*h g i := by rw [hsh]
    _ = _ := by
      have hc := (classWord_omegaPower_commute g (-(8 : ZMod d)⁻¹)
        ((h g i)⁻¹*(s g i)⁻¹*h g i^2)).symm.eq
      simp only [← mul_assoc]
      rw [hc]
      group

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Exact primitive-word Weyl commutation, with the Figure 1 omega scalar. -/
theorem derives_ZX (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g (Z (d := d) i ++ X (d := d) i)
      (omegaPower (1 : ZMod d) ++ X (d := d) i ++ Z (d := d) i) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using classWord_ZX g i

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Fourier pushing through the expanded Z word is an actual contextual derivation. -/
theorem derives_HZ (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g ([.H i] ++ Z (d := d) i)
      (inverseWord d (X (d := d) i) ++ [.H i]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append, classWord_inverseWord] using classWord_HZ g i

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Phase-gate pushing through the expanded X word is an actual contextual derivation. -/
theorem derives_SX (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    Derives g ([.S i] ++ X (d := d) i)
      (X (d := d) i ++ Z (d := d) i ++ [.S i]) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append] using classWord_SX g i

end QuditClifford.Circuit
