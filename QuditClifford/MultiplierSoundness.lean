import QuditClifford.ExpandedSoundness
import QuditClifford.GaussSign

/-! # Exact soundness of the fully expanded Figure 1 presentation

The classical Gauss-sign evaluation closes the multiplier denotation. Every
primitive rule and every contextual derivation now preserves exact matrices.
The intermediate conditional lemmas record how the scalar evaluation is used.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
variable {d n : ℕ} [NeZero d] [Fact d.Prime]

/-- The expanded primitive multiplier is its raw basis permutation times the
single dimension-dependent base Gauss sign. No sign has been discarded. -/
theorem denote_multiplier_eq_baseGaussSign (hd : Odd d)
    (i : Fin n) (a : (ZMod d)ˣ) :
    denote d (multiplier i a) = baseGaussSign d • onWire i (QuditClifford.multiplier d a) := by
  have hS (b : ZMod d) : QuditClifford.S d ^ b.val = phasePower d b := by
    rw [← phasePower_nat, ZMod.natCast_zmod_val]
  have hsign : (-1 : ℂ) ^ legendreSign a = complexQuadraticChar d (a : ZMod d) := by
    simpa only [legendreSign] using (complexQuadraticChar_eq_sign d a).symm
  have hZ : (1 - (a : ZMod d)) * (2 * (a : ZMod d))⁻¹ = multiplierZCorrection d a := by
    simp only [multiplierZCorrection, _root_.mul_inv_rev, half, Units.val_inv_eq_inv_val]
    ring
  have hX : (1 - (a : ZMod d)) * (2 : ZMod d)⁻¹ = multiplierXCorrection d a := rfl
  have hh := congrArg (onWire i) (multiplier_derived_eq_baseGaussSign d hd a)
  simp only [onWire_smul] at hh
  rw [← hh]
  simp only [multiplier, denote_append, denote_scalar, denote_omegaPower hd,
    denote_Zexp hd, denote_Xexp hd, denote_Sexp, denote_cons, denote_nil,
    Gate.denote, mul_one, Matrix.smul_mul, Matrix.mul_smul, one_mul,
    smul_smul, ← onWire_mul, pow_mul, scalarGenerator_pow_dimension d hd,
    hsign, hZ, hX, hS]
  rw [mul_comm (phase d _) (complexQuadraticChar d _)]
  congr 1
  apply congrArg (onWire i)
  simp only [multiplierWord, mul_assoc]

/-- Exact T1 denotation requires only the explicitly stated base Gauss sign. -/
theorem multiplier_word_sound_of_baseGaussSign (hd : Odd d)
    (hGauss : baseGaussSign d = 1) : MultiplierWordSound d n := by
  intro i a
  rw [denote_multiplier_eq_baseGaussSign hd, hGauss, one_smul]

/-- All fully expanded Figure 1 equations are sound, conditional solely on the
classical base Gauss-sign evaluation. Completeness is a separate obligation. -/
theorem figure1_sound_of_baseGaussSign (hd : Odd d)
    (hGauss : baseGaussSign d = 1) (g : (ZMod d)ˣ) : Figure1Sound (n := n) g :=
  figure1_sound_of_multiplier hd (multiplier_word_sound_of_baseGaussSign hd hGauss) g

/-- Exact T1: the fully expanded primitive multiplier word denotes the raw
basis permutation on its named wire, with every scalar retained. -/
theorem denote_multiplier (hd : Odd d) (i : Fin n) (a : (ZMod d)ˣ) :
    denote d (multiplier i a) = onWire i (QuditClifford.multiplier d a) := by
  rw [denote_multiplier_eq_baseGaussSign hd, baseGaussSign_eq_one d hd, one_smul]

/-- The exact expanded multiplier denotation in every arity. -/
theorem multiplier_word_sound (hd : Odd d) : MultiplierWordSound d n :=
  multiplier_word_sound_of_baseGaussSign hd (baseGaussSign_eq_one d hd)

/-- Every fully expanded Figure 1 schema is an exact complex-matrix identity
for odd prime dimension, including all signs and powers of the primitive -ω. -/
theorem figure1_rule_sound (hd : Odd d) (g : (ZMod d)ˣ)
    {u v : Word n} (hr : Figure1Rule g u v) : denote d u = denote d v :=
  figure1_rule_sound_of_multiplier hd (multiplier_word_sound hd) g hr

/-- Exact soundness of the paper's complete primitive Figure 1 presentation.
This proves soundness only; rewrite completeness remains a separate theorem. -/
theorem figure1_sound (hd : Odd d) (g : (ZMod d)ˣ) : Figure1Sound (n := n) g :=
  figure1_sound_of_multiplier hd (multiplier_word_sound hd) g

end QuditClifford.Circuit
