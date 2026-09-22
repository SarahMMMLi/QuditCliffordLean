import QuditClifford.NormalInduction

/-!
# The paper's literal recursive symplectic normal form

A normal word is a concrete Z-normal sweep, a concrete X-normal sweep, and a
normal word on the preceding wires. This is the syntax of Definition 3.2.
The main theorem establishes existence and uniqueness of its exponent action
over finite fields. Matrix-level implementation and rewrite completeness are
separate claims and are not asserted here.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
universe u
variable {K : Type u} [Field K]

/-- The exact recursive grammar in Definition 3.2, with concrete box labels. -/
inductive SymplecticNormalForm (K : Type u) [Field K] : ℕ → Type u
  | empty : SymplecticNormalForm K 0
  | step {n : ℕ} (Z : ZNormal K (n + 1)) (X : XNormal K (n + 1))
      (tail : SymplecticNormalForm K n) : SymplecticNormalForm K (n + 1)

namespace SymplecticNormalForm
variable [Finite K]

/-- Execute the concrete sweeps in circuit order, then recurse on preceding wires. -/
def equiv : {n : ℕ} → SymplecticNormalForm K n → WireSymplectic (K := K) n
  | 0, .empty => WireSymplectic.refl
  | _ + 1, .step Z X N => N.equiv.lift.comp (X.equiv.comp Z.equiv)

@[simp] theorem equiv_step_apply {n : ℕ} (Z : ZNormal K (n + 1))
    (X : XNormal K (n + 1)) (N : SymplecticNormalForm K n) (v : Wires K (n + 1)) :
    (step Z X N).equiv v = N.equiv.lift (X.action (Z.action v)) := rfl

omit [Finite K] in
private theorem last_zx_pair (n : ℕ) :
    wiresBracket (lastVector (K := K) zVector n) (lastVector xVector n) = 1 := by
  simp [wiresBracket_last_left, lastVector_apply, bracket, zVector, xVector]

/-- Existence part of Proposition 3.8 for the actual recursively defined words. -/
theorem exists_equiv : (n : ℕ) → (f : WireSymplectic (K := K) n) →
    ∃ N : SymplecticNormalForm K n, N.equiv = f
  | 0, f => by
    refine ⟨.empty, ?_⟩
    apply WireSymplectic.ext
    intro v
    funext i
    exact Fin.elim0 i
  | n + 1, f => by
    let p := f.symm (lastVector zVector n)
    let q := f.symm (lastVector xVector n)
    have hpq : wiresBracket p q = 1 := by
      rw [f.symm.preserves]
      exact last_zx_pair n
    obtain ⟨⟨Z, X⟩, hZX, _⟩ := existsUnique_pair_normalizer p q hpq
    let L := X.equiv.comp Z.equiv
    have hLp : L p = lastVector zVector n := hZX.1
    have hLq : L q = lastVector xVector n := hZX.2
    have hLz : L.symm (lastVector zVector n) = p := by
      rw [← hLp, WireSymplectic.symm_apply_apply]
    have hLx : L.symm (lastVector xVector n) = q := by
      rw [← hLq, WireSymplectic.symm_apply_apply]
    let R := f.comp L.symm
    have hRz : R (lastVector zVector n) = lastVector zVector n := by
      change f (L.symm (lastVector zVector n)) = _
      rw [hLz]
      exact f.apply_symm_apply _
    have hRx : R (lastVector xVector n) = lastVector xVector n := by
      change f (L.symm (lastVector xVector n)) = _
      rw [hLx]
      exact f.apply_symm_apply _
    obtain ⟨N, hN⟩ := exists_equiv n (R.restrict hRz hRx)
    refine ⟨.step Z X N, ?_⟩
    apply WireSymplectic.ext
    intro v
    change N.equiv.lift (L v) = f v
    rw [hN, R.lift_restrict hRz hRx]
    change f (L.symm (L v)) = f v
    rw [WireSymplectic.symm_apply_apply]

/-- Uniqueness compares the actual A/B/D/E labels and then the smaller syntax. -/
theorem equiv_injective {n : ℕ} : Function.Injective (equiv : SymplecticNormalForm K n → _) := by
  intro N M h
  induction N with
  | empty => cases M; rfl
  | @step n Z X N ih =>
    cases M with
    | step Z' X' M =>
      let L := X.equiv.comp Z.equiv
      let p := L.symm (lastVector zVector n)
      let q := L.symm (lastVector xVector n)
      have hpq : wiresBracket p q = 1 := by
        rw [L.symm.preserves]
        exact last_zx_pair n
      have hpair : X.action (Z.action p) = lastVector zVector n ∧
          X.action (Z.action q) = lastVector xVector n :=
        ⟨L.apply_symm_apply _, L.apply_symm_apply _⟩
      have hwholeZ : (step Z' X' M).equiv p = lastVector zVector n := by
        rw [← h, equiv_step_apply, hpair.1, WireSymplectic.lift_lastVector]
      have hwholeX : (step Z' X' M).equiv q = lastVector xVector n := by
        rw [← h, equiv_step_apply, hpair.2, WireSymplectic.lift_lastVector]
      have hpair' : X'.action (Z'.action p) = lastVector zVector n ∧
          X'.action (Z'.action q) = lastVector xVector n := by
        constructor
        · apply M.equiv.lift.toLinearEquiv.injective
          simpa only [WireSymplectic.lift_lastVector] using hwholeZ
        · apply M.equiv.lift.toLinearEquiv.injective
          simpa only [WireSymplectic.lift_lastVector] using hwholeX
      have hlabels : (Z, X) = (Z', X') :=
        (existsUnique_pair_normalizer p q hpq).unique hpair hpair'
      have hz := congrArg Prod.fst hlabels
      have hx := congrArg Prod.snd hlabels
      cases hz
      cases hx
      have htail : N.equiv = M.equiv := by
        apply WireSymplectic.ext
        intro v
        have hwhole := congrArg (fun F : WireSymplectic (K := K) (n + 1) =>
          F (L.symm (initialEmbed n v))) h
        change N.equiv.lift (L (L.symm (initialEmbed n v))) =
          M.equiv.lift (L (L.symm (initialEmbed n v))) at hwhole
        rw [WireSymplectic.apply_symm_apply, WireSymplectic.lift_initialEmbed,
          WireSymplectic.lift_initialEmbed] at hwhole
        have hh := congrArg Fin.init hwhole
        simpa only [initialEmbed_init] using hh
      have hNM := ih htail
      cases hNM
      rfl

/-- Proposition 3.8 at the exponent level: exactly one literal normal word
represents each symplectic equivalence. -/
theorem existsUnique_equiv {n : ℕ} (f : WireSymplectic (K := K) n) :
    ∃! N : SymplecticNormalForm K n, N.equiv = f := by
  obtain ⟨N, hN⟩ := exists_equiv n f
  exact ⟨N, hN, fun M hM => equiv_injective (hM.trans hN.symm)⟩

/-- The bijection needed to count the actual normal syntax. -/
def equivWireSymplectic (n : ℕ) : SymplecticNormalForm K n ≃ WireSymplectic (K := K) n :=
  Equiv.ofBijective equiv ⟨equiv_injective, fun f => exists_equiv n f⟩

end SymplecticNormalForm
end QuditClifford.NormalBoxes
