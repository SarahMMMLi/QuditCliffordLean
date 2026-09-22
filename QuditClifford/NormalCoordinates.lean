import QuditClifford.XNormal

/-!
# Connect the concrete normal circuits to the Pauli exponent space

The normal-box proofs use one `(z,x)` pair per wire. `PhaseSpace` stores all Z
coordinates followed by all X coordinates. The coordinate equivalence here
identifies these representations and transports Lemmas 3.4--3.7 to the
existing Pauli/symplectic definitions. These remain exponent-action results.
-/

noncomputable section
namespace QuditClifford.NormalBoxes

/-- Reorganize per-wire `(z,x)` pairs into the paper's `(z-vector,x-vector)` order. -/
def wiresCoordinates (d n : ℕ) : Wires (ZMod d) n ≃ₗ[ZMod d] PhaseSpace d n where
  toFun v := (fun i => (v i).1, fun i => (v i).2)
  invFun v := fun i => (v.1 i, v.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {d n : ℕ} [Fact d.Prime]

@[simp] theorem wiresCoordinates_symplectic (v w : Wires (ZMod d) n) :
    symplectic (wiresCoordinates d n v) (wiresCoordinates d n w) = wiresBracket v w := by
  simp [symplectic, dot, wiresCoordinates, wiresBracket, bracket, Finset.sum_sub_distrib]

@[simp] theorem wiresCoordinates_headZ :
    wiresCoordinates d (n + 1) (headZ n) = (exponentBasis 0, 0) := by
  apply Prod.ext <;> funext i <;> cases i using Fin.cases <;>
    simp [wiresCoordinates, headZ, zVector, exponentBasis]

variable {K : Type*} [Field K]

theorem lastVector_apply (v : Vector K) (n : ℕ) (i : Fin (n + 1)) :
    lastVector v n i = if i = Fin.last n then v else 0 := by
  induction n with
  | zero =>
    fin_cases i
    simp [lastVector]
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [lastVector, ← Fin.succ_last, (Fin.succ_ne_zero _).symm]
    | succ i => simp [lastVector, ← Fin.succ_last, ih]

@[simp] theorem wiresCoordinates_lastZ :
    wiresCoordinates d (n + 1) (lastVector zVector n) = (exponentBasis (Fin.last n), 0) := by
  apply Prod.ext <;> funext i <;>
    simp [wiresCoordinates, lastVector_apply, zVector, exponentBasis, apply_ite Prod.fst,
      apply_ite Prod.snd]

@[simp] theorem wiresCoordinates_lastX :
    wiresCoordinates d (n + 1) (lastVector xVector n) = (0, exponentBasis (Fin.last n)) := by
  apply Prod.ext <;> funext i <;>
    simp [wiresCoordinates, lastVector_apply, xVector, exponentBasis, apply_ite Prod.fst,
      apply_ite Prod.snd]

/-- Execute a concrete Z-normal word on the existing exponent-space coordinates. -/
def ZNormal.phaseAction (N : ZNormal (ZMod d) n) (v : PhaseSpace d n) : PhaseSpace d n :=
  wiresCoordinates d n (N.action ((wiresCoordinates d n).symm v))

/-- Execute a concrete X-normal word on the existing exponent-space coordinates. -/
def XNormal.phaseAction (N : XNormal (ZMod d) n) (v : PhaseSpace d n) : PhaseSpace d n :=
  wiresCoordinates d n (N.action ((wiresCoordinates d n).symm v))

theorem ZNormal.phaseAction_preserves (N : ZNormal (ZMod d) n) :
    PreservesSymplectic N.phaseAction := by
  intro v w
  rw [ZNormal.phaseAction, ZNormal.phaseAction, wiresCoordinates_symplectic, N.preserves]
  exact (wiresCoordinates_symplectic ((wiresCoordinates d n).symm v)
    ((wiresCoordinates d n).symm w)).symm

theorem XNormal.phaseAction_preserves (N : XNormal (ZMod d) n) :
    PreservesSymplectic N.phaseAction := by
  intro v w
  rw [XNormal.phaseAction, XNormal.phaseAction, wiresCoordinates_symplectic, N.preserves]
  exact (wiresCoordinates_symplectic ((wiresCoordinates d n).symm v)
    ((wiresCoordinates d n).symm w)).symm

/-- Lemma 3.4 in the existing exponent-space coordinates. -/
theorem ZNormal.existsUnique_phaseNormalizer (v : PhaseSpace d (n + 1)) (hv : v ≠ 0) :
    ∃! N : ZNormal (ZMod d) (n + 1), N.phaseAction v = (exponentBasis 0, 0) := by
  have hcoord : (wiresCoordinates d (n + 1)).symm v ≠ 0 := by
    intro h
    apply hv
    simpa using congrArg (wiresCoordinates d (n + 1)) h
  obtain ⟨N, hN, huniq⟩ := existsUnique_normalizer _ hcoord
  refine ⟨N, ?_, ?_⟩
  · change N.phaseAction v = _
    rw [phaseAction, hN, wiresCoordinates_headZ]
  · intro M hM
    apply huniq
    apply (wiresCoordinates d (n + 1)).injective
    simpa only [wiresCoordinates_headZ] using hM

/-- Lemma 3.7 in the existing exponent-space coordinates, without oddness. -/
theorem existsUnique_phasePairNormalizer (p q : PhaseSpace d (n + 1))
    (hpq : symplectic p q = 1) :
    ∃! N : ZNormal (ZMod d) (n + 1) × XNormal (ZMod d) (n + 1),
      N.2.phaseAction (N.1.phaseAction p) = (exponentBasis (Fin.last n), 0) ∧
      N.2.phaseAction (N.1.phaseAction q) = (0, exponentBasis (Fin.last n)) := by
  let e := wiresCoordinates d (n + 1)
  have hpqw : wiresBracket (e.symm p) (e.symm q) = 1 := by
    rw [← wiresCoordinates_symplectic]
    simpa [e] using hpq
  obtain ⟨N, hN, huniq⟩ := existsUnique_pair_normalizer (e.symm p) (e.symm q) hpqw
  have hequiv (M : ZNormal (ZMod d) (n + 1) × XNormal (ZMod d) (n + 1)) :
      (M.2.phaseAction (M.1.phaseAction p) = (exponentBasis (Fin.last n), 0) ∧
       M.2.phaseAction (M.1.phaseAction q) = (0, exponentBasis (Fin.last n))) ↔
      (M.2.action (M.1.action (e.symm p)) = lastVector zVector n ∧
       M.2.action (M.1.action (e.symm q)) = lastVector xVector n) := by
    simp only [ZNormal.phaseAction, XNormal.phaseAction, LinearEquiv.symm_apply_apply]
    rw [← wiresCoordinates_lastZ, ← wiresCoordinates_lastX]
    exact and_congr e.injective.eq_iff e.injective.eq_iff
  refine ⟨N, (hequiv N).mpr hN, ?_⟩
  intro M hM
  exact huniq M ((hequiv M).mp hM)

end QuditClifford.NormalBoxes
