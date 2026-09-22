import QuditClifford.GeneratedClifford
import QuditClifford.CyclotomicScalars

/-! # The exact scalar group and symplectic kernel of generated matrices

The generated matrix subgroup is used throughout. No quotient-surjectivity or
rewriting-completeness assumption enters the identification of its kernel.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
variable {d n : ℕ} [NeZero d] [Fact d.Prime]

/-- Every scalar in the actual generated matrix group is a power of -omega. -/
theorem generated_scalar_eq_scalarGenerator_pow (hd : Odd d)
    (U : generatedCliffordGroup d n) (c : ℂ)
    (hU : U.val.val = c • (1 : QuditOperator d n)) :
    ∃ r : ℕ, c = scalarGenerator d ^ r := by
  obtain ⟨w, hw⟩ := (mem_generated_iff hd U.val).mp U.property
  apply scalar_eq_scalarGenerator_pow hd w c
  exact (congrArg Subtype.val hw).trans hU

/-- The exact generated scalar group has precisely the canonical 2d exponents. -/
theorem generated_scalar_unique_power (hd : Odd d)
    (U : generatedCliffordGroup d n) (c : ℂ)
    (hU : U.val.val = c • (1 : QuditOperator d n)) :
    ∃! r : Fin (2*d), c = scalarGenerator d ^ r.val := by
  obtain ⟨w, hw⟩ := (mem_generated_iff hd U.val).mp U.property
  exact scalar_unique_power hd w c ((congrArg Subtype.val hw).trans hU)

/-- A generated matrix is scalar exactly when it is a power of the specified
Figure 1 scalar generator. -/
theorem generated_scalar_iff (hd : Odd d) (U : generatedCliffordGroup d n) :
    (∃ c : ℂ, U.val.val = c • (1 : QuditOperator d n)) ↔
      ∃ r : ℕ, U.val.val = scalarGenerator d ^ r • (1 : QuditOperator d n) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r, hr⟩ := generated_scalar_eq_scalarGenerator_pow hd U c hc
    exact ⟨r, hr ▸ hc⟩
  · rintro ⟨r, hr⟩
    exact ⟨scalarGenerator d ^ r, hr⟩

omit [Fact d.Prime] in
/-- Powers of the intrinsic signed-Pauli scalar have the exact scalar matrix. -/
theorem signed_repr_scalarGenerator_pow (k : ℕ) :
    SignedPauli.repr ((SignedPauli.scalarGenerator : SignedPauli d n)^k) =
      scalarGenerator d ^ k • (1 : QuditOperator d n) := by
  change SignedPauli.reprHom ((SignedPauli.scalarGenerator : SignedPauli d n)^k) = _
  rw [map_pow]
  change SignedPauli.repr (SignedPauli.scalarGenerator : SignedPauli d n)^k = _
  rw [SignedPauli.repr_scalarGenerator, smul_pow, one_pow]

omit [Fact d.Prime] in
/-- The signed group represents a primitive scalar power times any ordinary Pauli. -/
theorem signed_repr_scalarGenerator_pow_mul (k : ℕ) (p : Pauli d n) :
    SignedPauli.repr ((SignedPauli.scalarGenerator : SignedPauli d n)^k * (1, p)) =
      scalarGenerator d ^ k • Pauli.repr p := by
  rw [SignedPauli.repr_mul, signed_repr_scalarGenerator_pow, Matrix.smul_mul, one_mul]
  simp [SignedPauli.repr]

/-- Every symplectic-kernel element of the actual generated matrix group is an
actual signed Pauli, and every signed Pauli lies in that kernel. -/
theorem mem_generatedSymplecticHom_ker_iff_signedPauli (hd : Odd d)
    (U : generatedCliffordGroup d n) :
    U ∈ (generatedSymplecticHom hd).ker ↔
      ∃ p : SignedPauli d n, signedPauliToGenerated hd p = U := by
  rw [mem_generatedSymplecticHom_ker_iff]
  constructor
  · rintro ⟨p, c, _, hc⟩
    let V := U * pauliToGenerated hd p⁻¹
    have hV : V.val.val = c • (1 : QuditOperator d n) := by
      change U.val.val * (pauliToGenerated hd p⁻¹).val.val = _
      rw [pauliToGenerated_matrix, hc, Matrix.smul_mul, ← Pauli.repr_mul,
        mul_inv_cancel, Pauli.repr_one]
    obtain ⟨k, hk⟩ := generated_scalar_eq_scalarGenerator_pow hd V c hV
    refine ⟨(SignedPauli.scalarGenerator : SignedPauli d n)^k * (1, p), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [signedPauliToGenerated_matrix, signed_repr_scalarGenerator_pow_mul, ← hk]
    exact hc.symm
  · rintro ⟨p, rfl⟩
    refine ⟨p.2, phase 2 (Multiplicative.toAdd p.1), phase_ne_zero _ _, ?_⟩
    rw [signedPauliToGenerated_matrix]
    rfl

/-- The exact generated Clifford-to-symplectic kernel is the enlarged Pauli
subgroup selected by the user's Figure 1 -omega convention. -/
theorem generatedSymplecticHom_ker_eq_signedPauli_range (hd : Odd d) :
    (generatedSymplecticHom (d := d) (n := n) hd).ker =
      (signedPauliToGenerated hd).range := by
  ext U
  exact mem_generatedSymplecticHom_ker_iff_signedPauli hd U

end QuditClifford.Circuit
