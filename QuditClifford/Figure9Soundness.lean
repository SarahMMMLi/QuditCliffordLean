import QuditClifford.Figure9Syntax
import QuditClifford.AdjacentCompleteness

/-!
# Soundness of the corrected eighteen-rule Figure 9 presentation

Scalar erasure retains the exponent action. The common equations use already
proved Figure 1 soundness; the four additional two/three-wire equations are
checked directly on exponent coordinates. No Figure 9 completeness is used.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ}

/-- Removing scalar letters preserves the exponent action of a circuit. -/
@[simp] theorem symplecticAction_eraseScalar (w : Word n) (p : PhaseSpace d n) :
    symplecticAction d (eraseScalar w) p = symplecticAction d w p := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => cases a <;> simp [Gate.symplecticAction, ih]

/-- The reverse controlled addition T6 acts on the opposite ordered pair. -/
@[simp] theorem symplecticAction_XC (i j : Fin n) (hij : i ≠ j) (v : PhaseSpace d n) :
    symplecticAction d (XC i j hij) v = controlledAdd j i 1 v := by
  simp only [XC, symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction]
  apply Prod.ext <;> funext k <;>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [localHadamard, controlledPhase, controlledAdd, exponentBasis, hi, hj, hij, hij.symm]
  all_goals ring

variable [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

private theorem figure1Rule_symplecticSound (hd : Odd d) {u v : Word n}
    (h : Figure1Rule g u v) (p : PhaseSpace d n) :
    symplecticAction d u p = symplecticAction d v p :=
  symplecticRules_sound hd g (Or.inl (Or.inl (Or.inr h))) p

/-- Each corrected Figure 9 equation preserves the symplectic exponent action. -/
theorem figure9Rule_sound (hd : Odd d) {u v : Word n}
    (h : Figure9Rule g u v) (p : PhaseSpace d n) :
    symplecticAction d u p = symplecticAction d v p := by
  cases h with
  | C1 i => exact figure1Rule_symplecticSound g hd (.C1 i) p
  | C2 i =>
      simpa only [symplecticAction_eraseScalar, symplecticAction_append,
        symplecticAction_scalar] using figure1Rule_symplecticSound g hd (.C2 i) p
  | C3 i k =>
      simpa only [← eraseScalar_power, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C3 i k) p
  | C4 i =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar,
        symplecticAction_Zexp] using figure1Rule_symplecticSound g hd (.C4 i) p
  | C5 i => exact figure1Rule_symplecticSound g hd (.C5 i) p
  | C6 i j hij => exact figure1Rule_symplecticSound g hd (.C6 i j hij) p
  | C7 i j hij =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C7 i j hij) p
  | C8 i j hij => exact figure1Rule_symplecticSound g hd (.C8 i j hij) p
  | C9 i j hij =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C9 i j hij) p
  | C10 i j hij =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C10 i j hij) p
  | C11 i j hij =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C11 i j hij) p
  | C12 i j hij =>
      simp only [symplecticAction_append, symplecticAction_eraseScalar,
        symplecticAction_SWAP, symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction]
      apply Prod.ext <;> funext k <;>
        by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp [swapAction, controlledPhase, exponentBasis, Equiv.swap_apply_def,
          hi, hj, hij, hij.symm]
  | C13 i j hij =>
      have hpred : ((d-1 : ℕ) : ZMod d) = -1 := by
        rw [Nat.cast_sub (NeZero.pos d), Nat.cast_one, ZMod.natCast_self]
        ring
      simp only [symplecticAction_append, symplecticAction_XC,
        symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction,
        symplecticAction_replicate_CZ, hpred]
      apply Prod.ext <;> funext k <;>
        by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp [controlledAdd, localPhaseShear, controlledPhase, exponentBasis,
          hi, hj, hij, hij.symm]
      all_goals ring
  | C14 i j hij =>
      simp only [symplecticAction_append, symplecticAction_XC, symplecticAction_Sexp,
        symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction]
      apply Prod.ext <;> funext k <;>
        by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp [controlledAdd, localPhaseShear, controlledPhase, exponentBasis,
          hi, hj, hij, hij.symm]
      all_goals ring
  | C15 i j k hij hjk hik =>
      simp only [symplecticAction_cons, symplecticAction_nil, Gate.symplecticAction]
      apply Prod.ext <;> funext l <;>
        by_cases hi : l = i <;> by_cases hj : l = j <;> by_cases hk : l = k <;>
        simp [controlledPhase, exponentBasis, hi, hj, hk, hij, hij.symm, hjk,
          hjk.symm, hik, hik.symm]
      all_goals ring
  | C16 i j k hij hjk hik =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C13 i j k hij hjk hik) p
  | C17 i j k hij hjk hik =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C14 i j k hij hjk hik) p
  | C18 i j k hij hjk hik =>
      simpa only [symplecticAction_append, symplecticAction_eraseScalar] using
        figure1Rule_symplecticSound g hd (.C15 i j k hij hjk hik) p

/-- The guarded source equations, including structural wiring, are sound. -/
theorem figure9Rules_sound (hd : Odd d) {u v : Word n}
    (h : Figure9Rules g u v) (p : PhaseSpace d n) :
    symplecticAction d u p = symplecticAction d v p := by
  rcases h.1 with h | h
  · exact symplecticRules_sound hd g (Or.inl (Or.inl (Or.inl h))) p
  · exact figure9Rule_sound g hd h p

/-- Every contextual Figure 9 derivation preserves exponent action. -/
theorem figure9Derives_sound (hd : Odd d) {u v : Word n}
    (h : Figure9Derives g u v) (p : PhaseSpace d n) :
    symplecticAction d u p = symplecticAction d v p := by
  induction h generalizing p with
  | refl w => rfl
  | rule h => exact figure9Rules_sound g hd h p
  | symm h ih => exact (ih p).symm
  | trans h k ih ik => exact (ih p).trans (ik p)
  | context l r h ih => simp only [symplecticAction_append, ih]

variable [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Figure 9 rewrites map into the independently proved complete adjacent
Figure 1 presentation with explicit scalar and Pauli erasure. -/
theorem figure9Derives_adjacentSymplectic {u v : Word n}
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) (h : Figure9Derives g u v) :
    AdjacentSymplecticDerives g u v :=
  adjacentSymplecticErasureComplete g n u v hu hv
    (fun p => figure9Derives_sound g Fact.out h p)

end QuditClifford.Circuit
