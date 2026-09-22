import QuditClifford.MultiplierRewrites
import QuditClifford.SymplecticRewrites
import QuditClifford.NormalCircuit

/-!
# Syntactic one-wire box rewrites

These are contextual derivations for the concrete Figure 6 words. The first
three cases already hold exactly, without scalar or Pauli erasure. They are
proved in the quotient by Figure 1 derivations, never from matrix equality.
-/

noncomputable section
namespace QuditClifford.Circuit

variable {d n : ℕ} [NeZero d]

/-- The primitive S class has order dividing d, directly by C1. -/
theorem classWord_S_order (g : (ZMod d)ˣ) (i : Fin n) :
    classWord g [.S i] ^ d = 1 := by
  have h := (classWord_eq_iff_derives g (List.replicate d (.S i)) []).mpr
    (.rule (Or.inr (Figure1Rule.C1 i)))
  simpa only [classWord_replicate, classWord_nil] using h

/-- Addition of field-valued S exponents is justified by the C1 relation. -/
theorem classWord_Sexp_add (g : (ZMod d)ˣ) (i : Fin n) (a b : ZMod d) :
    classWord g (Sexp i (a+b)) = classWord g (Sexp i a) * classWord g (Sexp i b) := by
  simp only [Sexp, classWord_replicate, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod (a.val+b.val) (classWord_S_order g i)).symm

/-- Contextual C1 derivation of addition of S exponents. -/
theorem derives_Sexp_add (g : (ZMod d)ˣ) (i : Fin n) (a b : ZMod d) :
    Derives g (Sexp i a ++ Sexp i b) (Sexp i (a+b)) := by
  apply (classWord_eq_iff_derives g _ _).mp
  exact (classWord_Sexp_add g i a b).symm

variable [Fact d.Prime]

/-- Appending a single S increments its residue-valued exponent. -/
theorem derives_Sexp_S (g : (ZMod d)ˣ) (i : Fin n) (a : ZMod d) :
    Derives g (Sexp i a ++ [.S i]) (Sexp i (a+1)) := by
  have ho : (1 : ZMod d).val = 1 := ZMod.val_one d
  simpa only [Sexp, ho, List.replicate_one] using derives_Sexp_add g i a 1

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [Fact d.Prime] [NeZero d]

/-- The A-label after the zero-a Fourier case. -/
def ABox.hadamardZero (A : ABox (ZMod d)) (ha : A.a = 0) : ABox (ZMod d) :=
  ⟨A.b, 0, fun h => A.b_ne_zero ha (congrArg Prod.snd h)⟩

/-- The A-label after appending S. -/
def ABox.phaseStep (A : ABox (ZMod d)) (ha : A.a ≠ 0) : ABox (ZMod d) :=
  ⟨A.a, A.b-A.a, fun h => ha (congrArg Prod.snd h)⟩

omit [NeZero d] in
/-- Appendix F's first one-wire case, by the literal Figure 6 definitions. -/
theorem ABox.toWord_H_zero (A : ABox (ZMod d)) (ha : A.a = 0) (i : Fin n) :
    A.toWord i ++ [.H i] = (A.hadamardZero ha).toWord i := by
  simp [ABox.toWord, ha, ABox.hadamardZero, A.b_ne_zero ha, Sexp]

/-- The first H-through-A case is an exact syntactic derivation. -/
theorem derives_A_H_zero (g : (ZMod d)ˣ) (A : ABox (ZMod d))
    (ha : A.a = 0) (i : Fin n) :
    Derives g (A.toWord i ++ [.H i]) ((A.hadamardZero ha).toWord i) := by
  rw [A.toWord_H_zero ha]
  exact .refl _

/-- The nonzero-a S-through-A case, using exponent addition rather than semantics. -/
theorem derives_A_S_nonzero (g : (ZMod d)ˣ) (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (i : Fin n) :
    Derives g (A.toWord i ++ [.S i]) ((A.phaseStep ha).toWord i) := by
  have hexp : -A.b / A.a + 1 = -(A.b-A.a) / A.a := by
    field_simp
    ring
  have hr := (derives_Sexp_S g i (-A.b/A.a)).append_left
      (Circuit.multiplier i (Units.mk0 A.a ha) ++ [.H i])
  rw [hexp] at hr
  change Derives g ((if h : A.a = 0 then _ else _) ++ [.S i])
    (if h : A.a = 0 then _ else _)
  simp only [dif_neg ha, List.append_assoc] at *
  exact hr

/-- The E-through-S case from Appendix F, as an exact contextual rewrite. -/
theorem derives_E_S (g : (ZMod d)ˣ) (b : ZMod d) (i : Fin n) :
    Derives g (eWord b i ++ [.S i]) (eWord (b-1) i) := by
  have hexp : -b+1 = -(b-1) := by ring
  simpa only [eWord, hexp] using derives_Sexp_S g i (-b)

end QuditClifford.NormalBoxes

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

set_option linter.unusedSectionVars false in
/-- S exponent addition survives explicit scalar and Pauli erasure. -/
theorem symplecticClassWord_Sexp_add (i : Fin n) (a b : ZMod d) :
    symplecticClassWord g (Sexp i (a+b)) =
      symplecticClassWord g (Sexp i a) * symplecticClassWord g (Sexp i b) := by
  simpa using congrArg (presentedToSymplectic g) (classWord_Sexp_add g i a b)

set_option linter.unusedSectionVars false in
@[simp] theorem symplecticClassWord_Sexp_zero (i : Fin n) :
    symplecticClassWord g (Sexp i (0 : ZMod d)) = 1 := by simp [Sexp]

@[simp] theorem symplecticClassWord_Sexp_one (i : Fin n) :
    symplecticClassWord g (Sexp i (1 : ZMod d)) = symplecticClassWord g [.S i] := by
  simp [Sexp, ZMod.val_one]

/-- Multiplication of a field exponent is repeated composition, using C1. -/
theorem symplecticClassWord_Sexp_nsmul (i : Fin n) (a : ZMod d) (k : ℕ) :
    symplecticClassWord g (Sexp i ((k : ZMod d)*a)) =
      symplecticClassWord g (Sexp i a)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      symplecticClassWord_Sexp_add, ih, pow_succ]

/-- Multipliers obey the all-unit product law in the erased syntactic quotient. -/
theorem symplecticClassWord_multiplier_mul (hg : orderOf g = d-1)
    (i : Fin n) (a b : (ZMod d)ˣ) :
    symplecticClassWord g (multiplier i (a*b)) =
      symplecticClassWord g (multiplier i a) * symplecticClassWord g (multiplier i b) := by
  simpa using congrArg (presentedToSymplectic g) (classWord_multiplier_mul g hg i a b)

/-- C4, with its displayed Pauli correction explicitly erased. -/
theorem symplecticClassWord_multiplier_g_S (i : Fin n) :
    symplecticClassWord g (multiplier i g) * symplecticClassWord g [.S i] =
      symplecticClassWord g (Sexp i ((↑g⁻¹ : ZMod d)^2)) *
        symplecticClassWord g (multiplier i g) := by
  have h := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (show Derives g _ _ from .rule (Or.inr (Figure1Rule.C4 i))))
  simpa only [symplecticClassWord_append, symplecticClassWord_Zexp, one_mul] using h

/-- C4 conjugates arbitrary S powers after explicit Pauli erasure. -/
theorem symplecticClassWord_multiplier_g_Sexp (i : Fin n) (a : ZMod d) :
    symplecticClassWord g (multiplier i g) * symplecticClassWord g (Sexp i a) =
      symplecticClassWord g (Sexp i (a * (↑g⁻¹ : ZMod d)^2)) *
        symplecticClassWord g (multiplier i g) := by
  have h := SemiconjBy.pow_right (symplecticClassWord_multiplier_g_S g i) a.val
  change symplecticClassWord g (multiplier i g) * symplecticClassWord g [.S i] ^a.val =
    symplecticClassWord g (Sexp i ((↑g⁻¹ : ZMod d)^2))^a.val *
      symplecticClassWord g (multiplier i g) at h
  rw [← symplecticClassWord_Sexp_nsmul, ZMod.natCast_zmod_val] at h
  simpa only [Sexp, symplecticClassWord_replicate] using h

/-- Iterating C4 transports S through every power of the multiplier generator. -/
theorem symplecticClassWord_multiplier_gpow_Sexp (i : Fin n) (k : ℕ) (a : ZMod d) :
    symplecticClassWord g (multiplier i g)^k * symplecticClassWord g (Sexp i a) =
      symplecticClassWord g (Sexp i (a * (↑g⁻¹ : ZMod d)^(2*k))) *
        symplecticClassWord g (multiplier i g)^k := by
  induction k generalizing a with
  | zero => simp only [pow_zero, one_mul, mul_one, zero_mul, mul_zero, pow_zero, mul_one]
  | succ k ih =>
    rw [pow_succ, mul_assoc, symplecticClassWord_multiplier_g_Sexp, ← mul_assoc, ih]
    have he : (a * (↑g⁻¹ : ZMod d)^2) * (↑g⁻¹ : ZMod d)^(2*k) =
        a * (↑g⁻¹ : ZMod d)^(2*(k+1)) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [he, mul_assoc, ← pow_succ]

/-- The all-unit multiplier/S law is derived from finite C3 and primitive-root C4. -/
theorem symplecticClassWord_multiplier_Sexp (hg : orderOf g = d-1)
    (i : Fin n) (b : (ZMod d)ˣ) (a : ZMod d) :
    symplecticClassWord g (multiplier i b) * symplecticClassWord g (Sexp i a) =
      symplecticClassWord g (Sexp i (a * (↑b⁻¹ : ZMod d)^2)) *
        symplecticClassWord g (multiplier i b) := by
  obtain ⟨k,rfl⟩ := exists_generator_power g hg b
  have hm := congrArg (presentedToSymplectic g) (classWord_multiplier_gpow g hg i k)
  simp only [presentedToSymplectic_classWord, map_pow] at hm
  have hx : (↑(g^k)⁻¹ : ZMod d)^2 = (↑g⁻¹ : ZMod d)^(2*k) := by
    rw [← inv_pow, Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm k 2]
  rw [hm, hx, symplecticClassWord_multiplier_gpow_Sexp]

end QuditClifford.Circuit

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev sh (i : Fin n) := symplecticClassWord g [.H i]
private abbrev ss (i : Fin n) (a : ZMod d) := symplecticClassWord g (Sexp i a)
private abbrev sm (i : Fin n) (a : (ZMod d)ˣ) := symplecticClassWord g (multiplier i a)

/-- The S exponent is an additive parameter in the erased syntactic group. -/
theorem symplecticClassWord_Sexp_neg (i : Fin n) (a : ZMod d) :
    symplecticClassWord g (Sexp i (-a)) = (symplecticClassWord g (Sexp i a))⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_left
  rw [← symplecticClassWord_Sexp_add, neg_add_cancel, symplecticClassWord_Sexp_zero]

set_option linter.unusedSectionVars false in
/-- C2 after its explicitly displayed scalar is erased. -/
theorem symplecticClassWord_H_sq (i : Fin n) :
    symplecticClassWord g [.H i] ^2 = symplecticClassWord g (multiplier (d := d) i (-1)) := by
  have he := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (show Derives g _ _ from .rule (Or.inr (Figure1Rule.C2 i))))
  change symplecticClassWord g [.H i] * symplecticClassWord g [.H i] =
    symplecticClassWord g (scalar (d*((d-1)/2))) *
      symplecticClassWord g (multiplier i (-1)) at he
  rw [symplecticClassWord_scalar, one_mul] at he
  exact he

private theorem sh_four (i : Fin n) : sh g i^4 = 1 := by
  have he := congrArg (presentedToSymplectic g)
    ((classWord_eq_iff_derives g _ _).mpr (derives_H_four Fact.out g Fact.out i))
  simpa only [presentedToSymplectic_classWord, symplecticClassWord_replicate,
    symplecticClassWord_nil] using he

private theorem sh_inv (i : Fin n) : (sh g i)⁻¹ = sm g i (-1) * sh g i := by
  have he : sh g i^2 = sm g i (-1) := symplecticClassWord_H_sq g i
  rw [← he]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ, ← pow_succ', sh_four]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- The exact multiplier definition simplifies only by the explicit deletions. -/
theorem symplecticClassWord_multiplier_expand (i : Fin n) (a : (ZMod d)ˣ) :
    symplecticClassWord g (multiplier i a) =
      symplecticClassWord g (Sexp i (↑a⁻¹ : ZMod d)) * symplecticClassWord g [.H i] *
      symplecticClassWord g (Sexp i (a : ZMod d)) * symplecticClassWord g [.H i] *
      symplecticClassWord g (Sexp i (↑a⁻¹ : ZMod d)) * symplecticClassWord g [.H i] := by
  simp only [multiplier, symplecticClassWord_append, symplecticClassWord_scalar,
    symplecticClassWord_omegaPower, symplecticClassWord_Zexp, symplecticClassWord_Xexp, one_mul]

/-- The genuine Bruhat H-S-H rewrite, obtained by solving the multiplier definition. -/
theorem symplecticClassWord_H_Sexp_H (i : Fin n) (x : (ZMod d)ˣ) :
    symplecticClassWord g [.H i] * symplecticClassWord g (Sexp i (x : ZMod d)) *
        symplecticClassWord g [.H i] =
      symplecticClassWord g (Sexp i (-(↑x⁻¹ : ZMod d))) *
        symplecticClassWord g (multiplier i (-x)) * symplecticClassWord g [.H i] *
          symplecticClassWord g (Sexp i (-(↑x⁻¹ : ZMod d))) := by
  change sh g i * ss g i (x : ZMod d) * sh g i =
    ss g i (-(↑x⁻¹ : ZMod d)) * sm g i (-x) * sh g i * ss g i (-(↑x⁻¹ : ZMod d))
  have hx : -x = x * (-1) := by simp
  have hm : sm g i (x * (-1)) = sm g i x * sm g i (-1) :=
    symplecticClassWord_multiplier_mul g Fact.out i x (-1)
  have hn : ss g i (-(↑x⁻¹ : ZMod d)) = (ss g i (↑x⁻¹ : ZMod d))⁻¹ :=
    symplecticClassWord_Sexp_neg g i _
  rw [hx, hm, hn]
  have hexp : sm g i x = ss g i (↑x⁻¹ : ZMod d) * sh g i *
      ss g i (x : ZMod d) * sh g i * ss g i (↑x⁻¹ : ZMod d) * sh g i :=
    symplecticClassWord_multiplier_expand g i x
  calc
    _ = (ss g i (↑x⁻¹ : ZMod d))⁻¹ * sm g i x * (sh g i)⁻¹ *
        (ss g i (↑x⁻¹ : ZMod d))⁻¹ := by rw [hexp]; group
    _ = _ := by rw [sh_inv]; group

/-- H-S-H with a multiplier prefix, in the physical X-scaling convention. -/
theorem symplecticClassWord_multiplier_H_Sexp_H (i : Fin n)
    (a x : (ZMod d)ˣ) :
    symplecticClassWord g (multiplier i a) * symplecticClassWord g [.H i] *
        symplecticClassWord g (Sexp i (x : ZMod d)) * symplecticClassWord g [.H i] =
      symplecticClassWord g (Sexp i (-(↑x⁻¹ : ZMod d) * (↑a⁻¹ : ZMod d)^2)) *
        symplecticClassWord g (multiplier i (a * (-x))) * symplecticClassWord g [.H i] *
          symplecticClassWord g (Sexp i (-(↑x⁻¹ : ZMod d))) := by
  calc
    _ = sm g i a * (sh g i * ss g i (x : ZMod d) * sh g i) := by group
    _ = sm g i a * (ss g i (-(↑x⁻¹ : ZMod d)) * sm g i (-x) * sh g i *
        ss g i (-(↑x⁻¹ : ZMod d))) := by rw [symplecticClassWord_H_Sexp_H]
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc,
        symplecticClassWord_multiplier_Sexp g Fact.out]
      rw [mul_assoc (ss g i _) (sm g i a) (sm g i (-x)),
        ← symplecticClassWord_multiplier_mul g Fact.out]

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Fourier rotates the nonzero A label by (a,b) ↦ (b,-a). -/
def ABox.hadamardStep (A : ABox (ZMod d)) : ABox (ZMod d) :=
  ⟨A.b, -A.a, fun h => A.nonzero (by
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    simp only [Prod.fst, Prod.snd, neg_eq_zero] at ha hb
    simp [ha, hb])⟩

/-- The b=0 H-through-A case, using C2 and the derived multiplier product. -/
theorem symplectic_A_H_nonzero_zero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (hb : A.b = 0) (i : Fin n) :
    SymplecticDerives g (A.toWord i ++ [.H i]) (A.hadamardStep.toWord i) := by
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  have hm : Units.mk0 A.a ha * (-1) = Units.mk0 (-A.a) (neg_ne_zero.mpr ha) := by
    ext
    simp
  simp only [ABox.toWord, dif_neg ha, ABox.hadamardStep, hb, ↓reduceDIte,
    neg_zero, zero_div, Sexp, ZMod.val_zero, List.replicate_zero, List.append_nil,
    symplecticClassWord_append, ← mul_assoc]
  rw [mul_assoc, ← pow_two, symplecticClassWord_H_sq,
    ← symplecticClassWord_multiplier_mul g Fact.out, hm]

omit [Fact (Odd d)] in
/-- The a=0 S-through-A case, using C3/C4 for an arbitrary unit. -/
theorem symplectic_A_S_zero (A : ABox (ZMod d))
    (ha : A.a = 0) (i : Fin n) :
    SymplecticDerives g (A.toWord i ++ [.S i])
      (Sexp i (A.b⁻¹^2) ++ A.toWord i) := by
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  rw [ABox.toWord, dif_pos ha, symplecticClassWord_append,
    symplecticClassWord_append, ← symplecticClassWord_Sexp_one (g := g) i]
  simpa only [one_mul, Units.val_inv_eq_inv_val, Units.val_mk0] using
    symplecticClassWord_multiplier_Sexp g Fact.out i (Units.mk0 A.b (A.b_ne_zero ha)) 1

/-- The nonzero/nonzero H-through-A case, by the syntactic Bruhat identity. -/
theorem symplectic_A_H_nonzero_nonzero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (hb : A.b ≠ 0) (i : Fin n) :
    SymplecticDerives g (A.toWord i ++ [.H i])
      (Sexp i ((A.a*A.b)⁻¹) ++ A.hadamardStep.toWord i) := by
  let au := Units.mk0 A.a ha
  let xu := Units.mk0 (-A.b/A.a) (div_ne_zero (neg_ne_zero.mpr hb) ha)
  have hmul : au * (-xu) = Units.mk0 A.b hb := by
    ext
    dsimp [au, xu]
    field_simp
  have hexp : -(↑xu⁻¹ : ZMod d) * (↑au⁻¹ : ZMod d)^2 = (A.a*A.b)⁻¹ := by
    dsimp [au, xu]
    field_simp
    ring
  have hlast : -(↑xu⁻¹ : ZMod d) = -(-A.a)/A.b := by
    dsimp [xu]
    field_simp
  have h := symplecticClassWord_multiplier_H_Sexp_H g i au xu
  rw [hmul, hexp, hlast] at h
  apply (symplecticClassWord_eq_iff_derives g _ _).mp
  simpa only [ABox.toWord, dif_neg ha, ABox.hadamardStep, dif_neg hb,
    symplecticClassWord_append, List.append_assoc, au, xu, Units.val_mk0,
    mul_assoc] using h

/-- Exhaustive H-through-A normalization to a dirty S power and a new A box. -/
theorem symplectic_A_H (A : ABox (ZMod d)) (i : Fin n) :
    ∃ (c : ZMod d) (A' : ABox (ZMod d)),
      SymplecticDerives g (A.toWord i ++ [.H i]) (Sexp i c ++ A'.toWord i) := by
  by_cases ha : A.a = 0
  · refine ⟨0, A.hadamardZero ha, ?_⟩
    simpa only [Sexp, ZMod.val_zero, List.replicate_zero, List.nil_append] using
      derives_symplectic g (derives_A_H_zero g A ha i)
  · by_cases hb : A.b = 0
    · refine ⟨0, A.hadamardStep, ?_⟩
      simpa only [Sexp, ZMod.val_zero, List.replicate_zero, List.nil_append] using
        symplectic_A_H_nonzero_zero g A ha hb i
    · exact ⟨(A.a*A.b)⁻¹, A.hadamardStep, symplectic_A_H_nonzero_nonzero g A ha hb i⟩

omit [Fact (Odd d)] in
/-- Exhaustive S-through-A normalization to a dirty S power and a new A box. -/
theorem symplectic_A_S (A : ABox (ZMod d)) (i : Fin n) :
    ∃ (c : ZMod d) (A' : ABox (ZMod d)),
      SymplecticDerives g (A.toWord i ++ [.S i]) (Sexp i c ++ A'.toWord i) := by
  by_cases ha : A.a = 0
  · exact ⟨A.b⁻¹^2, A, symplectic_A_S_zero g A ha i⟩
  · refine ⟨0, A.phaseStep ha, ?_⟩
    simpa only [Sexp, ZMod.val_zero, List.replicate_zero, List.nil_append] using
      derives_symplectic g (derives_A_S_nonzero g A ha i)

end QuditClifford.NormalBoxes

namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Pauli Z erasure makes H squared commute with arbitrary S powers. -/
theorem symplecticClassWord_H_sq_commute_Sexp (i : Fin n) (a : ZMod d) :
    Commute (symplecticClassWord g [.H i] ^2) (symplecticClassWord g (Sexp i a)) := by
  have hi : (sh g i^2)⁻¹ = sh g i^2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    exact sh_four g i
  have hz := symplecticClassWord_Z g i
  change sh g i * sh g i * symplecticClassWord g [.S i] * sh g i * sh g i *
    ss g i (-1) = 1 at hz
  have hs : ss g i (-1) = (symplecticClassWord g [.S i])⁻¹ := by
    rw [ss, symplecticClassWord_Sexp_neg, symplecticClassWord_Sexp_one]
  rw [hs] at hz
  have hh : sh g i^2 * symplecticClassWord g [.S i] * sh g i^2 =
      symplecticClassWord g [.S i] := by
    apply (mul_inv_eq_one.mp)
    simpa only [pow_two, mul_assoc] using hz
  have hc : Commute (sh g i^2) (symplecticClassWord g [.S i]) := by
    show sh g i^2 * symplecticClassWord g [.S i] = symplecticClassWord g [.S i] * sh g i^2
    calc
      _ = (sh g i^2 * symplecticClassWord g [.S i] * sh g i^2) * (sh g i^2)⁻¹ := by group
      _ = _ := by rw [hh, hi]
  simpa only [Sexp, symplecticClassWord_replicate] using hc.pow_right a.val

/-- Raw multipliers conjugate across H by inversion of their unit parameter. -/
theorem symplecticClassWord_multiplier_H (i : Fin n) (a : (ZMod d)ˣ) :
    symplecticClassWord g (multiplier i a) * symplecticClassWord g [.H i] =
      symplecticClassWord g [.H i] * symplecticClassWord g (multiplier i a⁻¹) := by
  have hm : sm g i a * sm g i a⁻¹ = 1 := by
    rw [← symplecticClassWord_multiplier_mul g Fact.out, mul_inv_cancel]
    exact (symplecticClassWord_eq_iff_derives g _ _).mpr
      (derives_symplectic g (derives_multiplier_one g i))
  have hmi : sm g i a⁻¹ = (sm g i a)⁻¹ := (eq_inv_of_mul_eq_one_right hm)
  have hmneg : sm g i (-a) * sh g i^2 = sm g i a := by
    rw [symplecticClassWord_H_sq, ← symplecticClassWord_multiplier_mul g Fact.out]
    simp only [neg_mul_neg, mul_one]
  have hexp : sm g i (-a) =
      (ss g i (↑a⁻¹ : ZMod d))⁻¹ * sh g i * (ss g i (a : ZMod d))⁻¹ *
        sh g i * (ss g i (↑a⁻¹ : ZMod d))⁻¹ * sh g i := by
    rw [sm, symplecticClassWord_multiplier_expand]
    simp only [Units.val_neg, inv_neg, symplecticClassWord_Sexp_neg]
  have hqa : Commute (sh g i^2) (ss g i (a : ZMod d)) :=
    symplecticClassWord_H_sq_commute_Sexp g i _
  have hh : (sh g i)⁻¹ = sh g i^2 * sh g i := by
    have ht := sh_inv g i
    have hsq : sh g i^2 = sm g i (-1) := symplecticClassWord_H_sq g i
    rw [← hsq] at ht
    exact ht
  have hmiddle : (sh g i)⁻¹ * (ss g i (a : ZMod d))⁻¹ * (sh g i)⁻¹ =
      sh g i * (ss g i (a : ZMod d))⁻¹ * sh g i := by
    calc
      _ = (sh g i)⁻¹ * ((ss g i (a : ZMod d))⁻¹ * sh g i^2) * sh g i := by
        rw [hh]
        group
      _ = (sh g i)⁻¹ * (sh g i^2 * (ss g i (a : ZMod d))⁻¹) * sh g i := by
        rw [hqa.inv_right.eq]
      _ = _ := by group
  have hbase : sm g i a = ss g i (↑a⁻¹ : ZMod d) * sh g i *
      ss g i (a : ZMod d) * sh g i * ss g i (↑a⁻¹ : ZMod d) * sh g i :=
    symplecticClassWord_multiplier_expand g i a
  have hconj : sh g i * (sm g i a)⁻¹ * (sh g i)⁻¹ = sm g i a := by
    calc
      _ = (ss g i (↑a⁻¹ : ZMod d))⁻¹ *
          ((sh g i)⁻¹ * (ss g i (a : ZMod d))⁻¹ * (sh g i)⁻¹) *
            (ss g i (↑a⁻¹ : ZMod d))⁻¹ * (sh g i)⁻¹ := by rw [hbase]; group
      _ = (ss g i (↑a⁻¹ : ZMod d))⁻¹ *
          (sh g i * (ss g i (a : ZMod d))⁻¹ * sh g i) *
            (ss g i (↑a⁻¹ : ZMod d))⁻¹ * (sh g i)⁻¹ := by rw [hmiddle]
      _ = sm g i (-a) * sh g i^2 := by rw [hexp, hh]; group
      _ = _ := hmneg
  change sm g i a * sh g i = sh g i * sm g i a⁻¹
  rw [hmi]
  have hr := congrArg (fun t => t * sh g i) hconj
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hr.symm

end QuditClifford.Circuit
