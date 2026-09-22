import QuditClifford.Pauli

/-!
# Pauli exponents and their symplectic form

The coordinate order `(z,x)` follows Definition 2.25 of the paper. The bilinear
form is `dot z x' - dot x z'`. Its link to commutation is proved for the abstract
Pauli model from `Pauli.lean`. The symplectic preservation results in this file
are exponent-level statements; they are not complex-matrix conjugation theorems.
-/

namespace QuditClifford

/-- The exponent space, with `Z` coordinates first and `X` coordinates second. -/
abbrev PhaseSpace (d n : ℕ) := (Fin n → ZMod d) × (Fin n → ZMod d)

/-- Definition 2.25, with the paper's `(z,x)` ordering. -/
def symplectic {d n : ℕ} (v w : PhaseSpace d n) : ZMod d :=
  dot v.1 w.2 - dot v.2 w.1

variable {d n : ℕ}

@[simp] theorem symplectic_zero_left (v : PhaseSpace d n) : symplectic 0 v = 0 := by
  simp [symplectic]

@[simp] theorem symplectic_zero_right (v : PhaseSpace d n) : symplectic v 0 = 0 := by
  simp [symplectic]

theorem symplectic_add_left (u v w : PhaseSpace d n) :
    symplectic (u + v) w = symplectic u w + symplectic v w := by
  simp only [symplectic, Prod.fst_add, Prod.snd_add, dot_add_left]
  abel

theorem symplectic_add_right (u v w : PhaseSpace d n) :
    symplectic u (v + w) = symplectic u v + symplectic u w := by
  simp only [symplectic, Prod.fst_add, Prod.snd_add, dot_add_right]
  abel

theorem symplectic_skew (v w : PhaseSpace d n) : symplectic v w = -symplectic w v := by
  simp only [symplectic]
  rw [dot_comm v.1 w.2, dot_comm v.2 w.1]
  abel

@[simp] theorem symplectic_self (v : PhaseSpace d n) : symplectic v v = 0 := by
  simp [symplectic, dot_comm v.1 v.2]

@[simp] theorem symplectic_neg_left (v w : PhaseSpace d n) :
    symplectic (-v) w = -symplectic v w := by simp [symplectic]; abel

@[simp] theorem symplectic_neg_right (v w : PhaseSpace d n) :
    symplectic v (-w) = -symplectic v w := by simp [symplectic]; abel

theorem dot_smul_left (a : ZMod d) (v w : Fin n → ZMod d) :
    dot (a • v) w = a * dot v w := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_smul_right (a : ZMod d) (v w : Fin n → ZMod d) :
    dot v (a • w) = a * dot v w := by
  rw [dot_comm, dot_smul_left, dot_comm]

theorem symplectic_smul_left (a : ZMod d) (v w : PhaseSpace d n) :
    symplectic (a • v) w = a * symplectic v w := by
  simp [symplectic, dot_smul_left, mul_sub]

theorem symplectic_smul_right (a : ZMod d) (v w : PhaseSpace d n) :
    symplectic v (a • w) = a * symplectic v w := by
  simp [symplectic, dot_smul_right, mul_sub]

/-- The standard symplectic bilinear form as a pair of linear maps. -/
def symplecticLinear : PhaseSpace d n →ₗ[ZMod d] PhaseSpace d n →ₗ[ZMod d] ZMod d where
  toFun v :=
    { toFun := symplectic v
      map_add' := symplectic_add_right v
      map_smul' := by intro a w; exact symplectic_smul_right a v w }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    exact symplectic_add_left u v w
  map_smul' a v := by
    apply LinearMap.ext
    intro w
    exact symplectic_smul_left a v w

namespace Pauli

/-- Forget the central phase, with the coordinate order from Definition 2.25. -/
def coords (p : Pauli d n) : PhaseSpace d n := (p.z, p.x)

@[simp] theorem coords_one : (1 : Pauli d n).coords = 0 := rfl
@[simp] theorem coords_mul (p q : Pauli d n) : (p * q).coords = p.coords + q.coords := rfl
@[simp] theorem coords_inv (p : Pauli d n) : p⁻¹.coords = -p.coords := rfl

/-- Forgetting the phase is a homomorphism into the additive exponent group. -/
def coordsHom : Pauli d n →* Multiplicative (PhaseSpace d n) where
  toFun p := Multiplicative.ofAdd p.coords
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coords_surjective : Function.Surjective (coords : Pauli d n → PhaseSpace d n) := by
  intro v
  exact ⟨⟨0, v.2, v.1⟩, rfl⟩

theorem coords_eq_iff (p q : Pauli d n) :
    p.coords = q.coords ↔ ∃ c : ZMod d, p = scalar c * q := by
  rw [← same_exponents_iff]
  simp only [coords, Prod.mk.injEq]
  exact and_comm

theorem coords_zero_iff (p : Pauli d n) :
    p.coords = 0 ↔ ∃ c : ZMod d, p = scalar c := by
  simpa using coords_eq_iff p 1

/-- The symplectic form records precisely the abstract Pauli commutator phase. -/
theorem commutatorPhase_eq_symplectic (p q : Pauli d n) :
    commutatorPhase p q = symplectic p.coords q.coords := by
  simp only [commutatorPhase, symplectic, coords]
  rw [dot_comm q.z p.x]

theorem commute_iff_symplectic (p q : Pauli d n) :
    p * q = q * p ↔ symplectic p.coords q.coords = 0 := by
  rw [commute_iff, commutatorPhase_eq_symplectic]

end Pauli

/-- Preservation property in Definition 2.25, separated from linearity. -/
def PreservesSymplectic (f : PhaseSpace d n → PhaseSpace d n) : Prop :=
  ∀ v w, symplectic (f v) (f w) = symplectic v w

namespace PreservesSymplectic

theorem id : PreservesSymplectic (id : PhaseSpace d n → PhaseSpace d n) := by
  intro v w
  rfl

theorem comp {f g : PhaseSpace d n → PhaseSpace d n}
    (hf : PreservesSymplectic f) (hg : PreservesSymplectic g) :
    PreservesSymplectic (f ∘ g) := by
  intro v w
  exact (hf (g v) (g w)).trans (hg v w)

end PreservesSymplectic

/-- Apply the exponent action of `H` on every wire: `(z,x) ↦ (x,-z)`.
This is the action specified by Lemma 2.23, without phases. -/
def hadamard (v : PhaseSpace d n) : PhaseSpace d n := (v.2, -v.1)

/-- Apply the exponent action of `S^a` on every wire. -/
def phaseShear (a : ZMod d) (v : PhaseSpace d n) : PhaseSpace d n :=
  (v.1 + a • v.2, v.2)

/-- Apply the exponent action of tableauMultiplier `M_a` on every wire. -/
def tableauMultiplier (a : (ZMod d)ˣ) (v : PhaseSpace d n) : PhaseSpace d n :=
  ((↑a⁻¹ : ZMod d) • v.1, (↑a : ZMod d) • v.2)

theorem hadamard_preserves : PreservesSymplectic (hadamard : PhaseSpace d n → _) := by
  intro v w
  simp [hadamard, symplectic]
  abel

theorem phaseShear_preserves (a : ZMod d) : PreservesSymplectic (phaseShear (n := n) a) := by
  intro v w
  simp only [phaseShear, symplectic, dot_add_left, dot_add_right,
    dot_smul_left, dot_smul_right]
  abel

theorem tableauMultiplier_preserves (a : (ZMod d)ˣ) : PreservesSymplectic (tableauMultiplier (n := n) a) := by
  intro v w
  simp only [tableauMultiplier, symplectic, dot_smul_left, dot_smul_right]
  simp [← mul_assoc]

theorem hadamard_four (v : PhaseSpace d n) : hadamard (hadamard (hadamard (hadamard v))) = v := by
  simp [hadamard]

theorem phaseShear_add (a b : ZMod d) (v : PhaseSpace d n) :
    phaseShear a (phaseShear b v) = phaseShear (a + b) v := by
  ext i <;> simp [phaseShear, add_smul]
  ring

theorem phaseShear_zero (v : PhaseSpace d n) : phaseShear 0 v = v := by
  simp [phaseShear]

theorem tableauMultiplier_mul (a b : (ZMod d)ˣ) (v : PhaseSpace d n) :
    tableauMultiplier a (tableauMultiplier b v) = tableauMultiplier (a * b) v := by
  ext i <;> simp [tableauMultiplier, mul_smul]
  ring

theorem tableauMultiplier_one (v : PhaseSpace d n) : tableauMultiplier 1 v = v := by
  simp [tableauMultiplier]

/-- Standard basis vector on wire `i`. -/
def exponentBasis (i : Fin n) : Fin n → ZMod d := fun j => if j = i then 1 else 0

@[simp] theorem dot_basis_right (v : Fin n → ZMod d) (i : Fin n) :
    dot v (exponentBasis i) = v i := by
  simp [dot, exponentBasis, mul_ite]

@[simp] theorem dot_basis_left (v : Fin n → ZMod d) (i : Fin n) :
    dot (exponentBasis i) v = v i := by
  rw [dot_comm, dot_basis_right]

/-- Pairing with the standard basis separates all exponent vectors. -/
theorem symplectic_ext (v w : PhaseSpace d n)
    (h : ∀ u, symplectic v u = symplectic w u) : v = w := by
  apply Prod.ext
  · funext i
    simpa [symplectic] using h (0, exponentBasis i)
  · funext i
    have hi := h (exponentBasis i, 0)
    simpa [symplectic] using hi

/-- Nondegeneracy holds without the paper's odd-prime restriction. -/
theorem symplectic_nondegenerate (v : PhaseSpace d n)
    (h : ∀ w, symplectic v w = 0) : v = 0 := by
  apply symplectic_ext v 0
  simpa using h

theorem PreservesSymplectic.injective {f : PhaseSpace d n → PhaseSpace d n}
    (h : PreservesSymplectic f) : Function.Injective f := by
  intro v w hvw
  apply symplectic_ext v w
  intro u
  rw [← h v u, ← h w u, hvw]

/-- The group of linear symplectic transformations, Definition 2.25. -/
def symplecticGroup (d n : ℕ) : Subgroup (PhaseSpace d n ≃ₗ[ZMod d] PhaseSpace d n) where
  carrier := {f | PreservesSymplectic f}
  one_mem' := PreservesSymplectic.id
  mul_mem' := by
    intro f g hf hg v w
    exact (hf (g v) (g w)).trans (hg v w)
  inv_mem' := by
    intro f hf v w
    have h := hf (f.symm v) (f.symm w)
    simpa using h.symm

/-- The symplectic form written as a sum of independent wire contributions. -/
theorem symplectic_eq_sum (v w : PhaseSpace d n) :
    symplectic v w = ∑ i, (v.1 i * w.2 i - v.2 i * w.1 i) := by
  simp [symplectic, dot, Finset.sum_sub_distrib]

/-- `H` acts on one specified wire, following Lemma 2.23. -/
def localHadamard (i : Fin n) (v : PhaseSpace d n) : PhaseSpace d n :=
  (fun j => if j = i then v.2 j else v.1 j,
   fun j => if j = i then -v.1 j else v.2 j)

/-- `S^a` acts on one specified wire, following Lemma 2.23. -/
def localPhaseShear (i : Fin n) (a : ZMod d) (v : PhaseSpace d n) : PhaseSpace d n :=
  (fun j => if j = i then v.1 j + a * v.2 j else v.1 j, v.2)

/-- `M_a` acts on one specified wire. -/
def localMultiplier (i : Fin n) (a : (ZMod d)ˣ) (v : PhaseSpace d n) : PhaseSpace d n :=
  (fun j => if j = i then (↑a⁻¹ : ZMod d) * v.1 j else v.1 j,
   fun j => if j = i then (↑a : ZMod d) * v.2 j else v.2 j)

theorem localHadamard_preserves (i : Fin n) : PreservesSymplectic (localHadamard (d := d) i) := by
  intro v w
  simp only [symplectic_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i <;> simp [localHadamard, h]
  ring

theorem localPhaseShear_preserves (i : Fin n) (a : ZMod d) :
    PreservesSymplectic (localPhaseShear i a) := by
  intro v w
  simp only [symplectic_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i <;> simp [localPhaseShear, h]
  ring

theorem localMultiplier_preserves (i : Fin n) (a : (ZMod d)ˣ) :
    PreservesSymplectic (localMultiplier i a) := by
  intro v w
  simp only [symplectic_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = i
  · simp only [localMultiplier, if_pos h]
    calc
      ↑a⁻¹ * v.1 j * (↑a * w.2 j) - ↑a * v.2 j * (↑a⁻¹ * w.1 j) =
          (↑a⁻¹ * ↑a : ZMod d) * (v.1 j * w.2 j) -
          (↑a * ↑a⁻¹ : ZMod d) * (v.2 j * w.1 j) := by ring
      _ = _ := by simp
  · simp [localMultiplier, h]

/-- Exponent action of `CZ^a` on wires `i,j`, from Lemma 2.24.
For a physical two-wire gate the caller should require `i ≠ j`. -/
def controlledPhase (i j : Fin n) (a : ZMod d) (v : PhaseSpace d n) : PhaseSpace d n :=
  (v.1 + (a * v.2 j) • exponentBasis i + (a * v.2 i) • exponentBasis j, v.2)

theorem controlledPhase_preserves (i j : Fin n) (a : ZMod d) :
    PreservesSymplectic (controlledPhase i j a) := by
  intro v w
  simp only [controlledPhase, symplectic, dot_add_left, dot_add_right,
    dot_smul_left, dot_smul_right, dot_basis_left, dot_basis_right]
  ring

theorem localHadamard_four (i : Fin n) (v : PhaseSpace d n) :
    localHadamard i (localHadamard i (localHadamard i (localHadamard i v))) = v := by
  apply Prod.ext <;> funext j <;> by_cases h : j = i <;> simp [localHadamard, h]

theorem localPhaseShear_add (i : Fin n) (a b : ZMod d) (v : PhaseSpace d n) :
    localPhaseShear i a (localPhaseShear i b v) = localPhaseShear i (a + b) v := by
  apply Prod.ext <;> funext j <;> by_cases h : j = i <;> simp [localPhaseShear, h]
  ring

theorem controlledPhase_add (i j : Fin n) (a b : ZMod d) (v : PhaseSpace d n) :
    controlledPhase i j a (controlledPhase i j b v) = controlledPhase i j (a + b) v := by
  apply Prod.ext <;> funext k <;> simp [controlledPhase, add_smul, add_mul]
  ring

end QuditClifford
