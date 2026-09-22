import QuditClifford.AdjacentCircuitInverses
import QuditClifford.MultiplierRewrites
import QuditClifford.PauliWeylRewrites

/-!
# Exact one-wire algebra replayed in the adjacent presentation

Every proof is first a derivation on `Word 1`, where all primitive words are
adjacent, and is then transported to the chosen wire. Existing syntactic
proofs supply the Weyl and multiplier-product templates. The all-unit phase
and Fourier templates use the already proved one-qudit completeness theorem
and independently established exact matrix equations; no higher-arity
completeness premise or semantic-equality rewrite generator is introduced.
-/
noncomputable section
namespace QuditClifford.Circuit

variable {d m n : ℕ}

/-- Relabeling preserves the literal positive-power inverse of a primitive. -/
theorem Gate.relabel_inverseWord (ι : Fin m ↪ Fin n) (a : Gate m) :
    Circuit.relabel ι (a.inverseWord d) = (a.relabel ι).inverseWord d := by
  cases a <;> simp only [Gate.inverseWord, relabel_replicate, Gate.relabel]

/-- Relabeling preserves the reversed sequence of literal primitive inverses. -/
theorem relabel_inverseWord (ι : Fin m ↪ Fin n) (w : Word m) :
    relabel ι (inverseWord d w) = inverseWord d (relabel ι w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [inverseWord_cons, relabel_append, ih, Gate.relabel_inverseWord, relabel_cons]

variable [NeZero d] [Fact d.Prime] (g : (ZMod d)ˣ)

/-- The all-unit multiplier product remains a derivation in the restricted relation. -/
theorem adjacentDerives_multiplier_mul (hg : orderOf g = d-1)
    (i : Fin n) (a b : (ZMod d)ˣ) :
    AdjacentDerives g (multiplier i a ++ multiplier i b) (multiplier i (a*b)) := by
  simpa only [relabel_append, relabel_multiplier, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_multiplier_mul g hg (0 : Fin 1) a b)

/-- The generator cycle is replayed at any selected register wire. -/
theorem adjacentDerives_multiplier_cycle (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g (power (multiplier i g) (d-1)) [] := by
  simpa only [relabel_power, relabel_multiplier, relabel_nil, singleWireEmbedding,
    Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_multiplier_cycle g hg (0 : Fin 1))

/-- Exact all-unit C4 with its Z correction, obtained from the proved one-qudit theorem. -/
theorem adjacentDerives_multiplier_S (hd : Odd d) (hg : orderOf g = d-1)
    (i : Fin n) (a : (ZMod d)ˣ) :
    AdjacentDerives g (multiplier i a ++ [.S i])
      (Zexp i ((1-(a : ZMod d)) * (2*(a : ZMod d)^2)⁻¹) ++
        Sexp i ((↑a⁻¹ : ZMod d)^2) ++ multiplier i a) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  have h : Derives g (multiplier (0 : Fin 1) a ++ [.S 0])
      (Zexp 0 ((1-(a : ZMod d)) * (2*(a : ZMod d)^2)⁻¹) ++
        Sexp 0 ((↑a⁻¹ : ZMod d)^2) ++ multiplier 0 a) :=
    figure1Complete_one g _ _ (C4_sound_of_multiplier hd (multiplier_word_sound hd) 0 a)
  simpa only [relabel_append, relabel_multiplier, relabel_cons, relabel_nil,
    relabel_Zexp, relabel_Sexp, Gate.relabel, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i h

private theorem multiplier_fourier_exact (a : (ZMod d)ˣ) :
    QuditClifford.multiplier d a * H d = H d * QuditClifford.multiplier d a⁻¹ := by
  ext row col
  have hr (k : ZMod d) : row=(a : ZMod d)*k ↔ (↑a⁻¹ : ZMod d)*row=k := by
    constructor
    · intro h; rw [h, Units.inv_mul_cancel_left]
    · intro h; rw [← h, Units.mul_inv_cancel_left]
  simp only [QuditClifford.multiplier]
  rw [matrix_mul_basisMap]
  simp only [QuditClifford.multiplier, Matrix.mul_apply, basisMap, ite_mul, one_mul, zero_mul]
  simp_rw [hr]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [H, Matrix.smul_apply, smul_eq_mul, fourierMatrix]
  congr 2
  ring

/-- Exact raw multipliers cross H with the inverse unit parameter. -/
theorem adjacentDerives_multiplier_H (hd : Odd d) (hg : orderOf g = d-1)
    (i : Fin n) (a : (ZMod d)ˣ) :
    AdjacentDerives g (multiplier i a ++ [.H i]) ([.H i] ++ multiplier i a⁻¹) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  have h : Derives g (multiplier (0 : Fin 1) a ++ [.H 0])
      ([.H 0] ++ multiplier 0 a⁻¹) := by
    apply figure1Complete_one g
    simp only [denote_append, denote_multiplier hd, denote_cons, denote_nil, mul_one,
      Gate.denote, ← onWire_mul]
    exact congrArg (onWire (0 : Fin 1)) (multiplier_fourier_exact a)
  simpa only [relabel_append, relabel_multiplier, relabel_cons, relabel_nil,
    Gate.relabel, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i h

/-- Exact Weyl commutation, retaining the primitive omega scalar word. -/
theorem adjacentDerives_ZX (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g (Z (d := d) i ++ X (d := d) i)
      (omegaPower (1 : ZMod d) ++ X (d := d) i ++ Z (d := d) i) := by
  simpa only [relabel_append, relabel_Z, relabel_X, relabel_omegaPower,
    singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_ZX g hd hg (0 : Fin 1))

/-- Exact Fourier pushing through Z in the restricted presentation. -/
theorem adjacentDerives_HZ (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g ([.H i] ++ Z (d := d) i)
      (inverseWord d (X (d := d) i) ++ [.H i]) := by
  simpa only [relabel_append, relabel_Z, relabel_X, relabel_inverseWord, relabel_cons,
    relabel_nil, Gate.relabel, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_HZ g hd hg (0 : Fin 1))

/-- Exact Fourier pushing through X in the restricted presentation. -/
theorem adjacentDerives_HX (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g ([.H i] ++ X (d := d) i) (Z (d := d) i ++ [.H i]) := by
  simpa only [relabel_append, relabel_Z, relabel_X, relabel_cons, relabel_nil,
    Gate.relabel, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_HX_eq_ZH g hd hg (0 : Fin 1))

/-- Exact phase pushing through X, including its Z correction. -/
theorem adjacentDerives_SX (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g ([.S i] ++ X (d := d) i)
      (X (d := d) i ++ Z (d := d) i ++ [.S i]) := by
  simpa only [relabel_append, relabel_Z, relabel_X, relabel_cons, relabel_nil,
    Gate.relabel, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_SX g hd hg (0 : Fin 1))

/-- The Z/S commutation template remains exact at any register wire. -/
theorem adjacentDerives_Z_S_commute (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g (Z (d := d) i ++ [.S i]) ([.S i] ++ Z (d := d) i) := by
  simpa only [relabel_append, relabel_Z, relabel_cons, relabel_nil,
    Gate.relabel, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_Z_S_commute g hd hg (0 : Fin 1))

/-- The expanded X word has its exact finite order in the restricted relation. -/
theorem adjacentDerives_X_order (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g (power (X (d := d) i) d) [] := by
  simpa only [relabel_power, relabel_X, relabel_nil, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_X_order g hd hg (0 : Fin 1))

/-- The expanded Z word has its exact finite order in the restricted relation. -/
theorem adjacentDerives_Z_order (hd : Odd d) (hg : orderOf g = d-1) (i : Fin n) :
    AdjacentDerives g (power (Z (d := d) i) d) [] := by
  simpa only [relabel_power, relabel_Z, relabel_nil, singleWireEmbedding, Function.Embedding.coeFn_mk]
    using adjacentDerives_singleWire g i (derives_Z_order g hd hg (0 : Fin 1))

end QuditClifford.Circuit
