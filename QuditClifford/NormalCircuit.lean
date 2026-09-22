import QuditClifford.CircuitRelabel
import QuditClifford.SymplecticNormalForm
import QuditClifford.SymplecticCoordinates

/-!
# Elaboration of the concrete normal boxes into the primitive circuit alphabet

All words below use only `-omega,H,S,CZ`, in matrix order. Derived multipliers,
controlled additions and swaps retain every scalar in their exact expansions.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [Fact d.Prime]

/-- Figure 6 A box as an exact primitive word on a specified wire. -/
def ABox.toWord (A : ABox (ZMod d)) (i : Fin n) : Circuit.Word n :=
  if h : A.a = 0 then Circuit.multiplier i (Units.mk0 A.b (A.b_ne_zero h))
  else Circuit.multiplier i (Units.mk0 A.a h) ++ [.H i] ++ Circuit.Sexp i (-A.b / A.a)

/-- Figure 6 E box. -/
def eWord (b : ZMod d) (i : Fin n) : Circuit.Word n := Circuit.Sexp i (-b)

/-- Figure 6 B box, including its exact SWAP and CX expansions. -/
def bWord (a b : ZMod d) (i j : Fin n) (hij : i ≠ j) : Circuit.Word n :=
  if a = 0 then Circuit.SWAP (d := d) i j hij ++ Circuit.power (Circuit.CX i j hij) b.val
  else Circuit.SWAP (d := d) i j hij ++ Circuit.power (Circuit.CX i j hij) a.val ++
    [.H i] ++ Circuit.Sexp i (-b / a)

/-- Figure 6 D box, including its exact SWAP expansion. -/
def dWord (a b : ZMod d) (i j : Fin n) (hij : i ≠ j) : Circuit.Word n :=
  if a = 0 then Circuit.SWAP (d := d) i j hij ++ List.replicate (-b).val (.CZ i j hij)
  else Circuit.SWAP (d := d) i j hij ++ List.replicate (-a).val (.CZ i j hij) ++
    [.H j] ++ Circuit.Sexp j (-b / a)

private theorem zero_ne_one (n : ℕ) : (0 : Fin (n + 2)) ≠ 1 := by
  intro h
  have hh := congrArg Fin.val h
  simp at hh

@[simp] private theorem succ_succ_ne_one (k : Fin n) : k.succ.succ ≠ (1 : Fin (n + 2)) := by
  intro h
  have hh := congrArg Fin.val h
  simp at hh

/-- Every exact A-box word realizes the previously proved concrete exponent action. -/
theorem ABox.toWord_action (A : ABox (ZMod d)) (i k : Fin n) (v : Wires (ZMod d) n) :
    Circuit.wireAction d (A.toWord i) v k = if k = i then A.action (v k) else v k := by
  by_cases ha : A.a = 0
  · simp only [ABox.toWord, dif_pos ha, Circuit.wireAction_multiplier,
      A.action_of_a_zero ha, Units.val_inv_eq_inv_val, Units.val_mk0]
    by_cases hk : k = i <;> simp only [hk, ite_true, ite_false]
    congr 1
    exact mul_comm _ _
  · simp only [ABox.toWord, dif_neg ha, Circuit.wireAction_append,
      Circuit.wireAction_cons, Circuit.wireAction_nil, Circuit.wireAction_multiplier,
      Circuit.Gate.wireAction_H, Circuit.wireAction_Sexp, A.action_of_a_ne_zero ha,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    by_cases hk : k = i <;> simp only [hk, ite_true, ite_false]
    apply Prod.ext <;> dsimp
    · ring
    · field_simp
      ring

@[simp] theorem eWord_action (b : ZMod d) (i k : Fin n) (v : Wires (ZMod d) n) :
    Circuit.wireAction d (eWord b i) v k = if k = i then eAction b (v k) else v k := by
  simp [eWord, eAction_apply, sub_eq_add_neg]

/-- The adjacent B word implements the concrete Figure 6 two-wire action. -/
theorem bWord_action (a b : ZMod d) (v : Wires (ZMod d) (n + 2)) :
    Circuit.wireAction d (bWord a b 0 1 (zero_ne_one n)) v =
      Fin.cons (bAction a b (v 0, v 1)).1
        (Fin.cons (bAction a b (v 0, v 1)).2 (Fin.tail (Fin.tail v))) := by
  by_cases ha : a = 0
  · subst a
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [bWord, Circuit.wireAction_append, Equiv.swap_apply_def, bAction_zero]
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp [bWord, Circuit.wireAction_append, Equiv.swap_apply_def, bAction_zero]
      · simp [bWord, Circuit.wireAction_append, Equiv.swap_apply_def, bAction_zero, Fin.tail]
  · funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [bWord, ha, Circuit.wireAction_append, Equiv.swap_apply_def, bAction_nonzero a b ha]
      field_simp
      ring
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp [bWord, ha, Circuit.wireAction_append, Equiv.swap_apply_def, bAction_nonzero a b ha]
        field_simp
        ring
      · simp [bWord, ha, Circuit.wireAction_append, Equiv.swap_apply_def, bAction_nonzero a b ha,
          Fin.tail]

/-- The adjacent D word implements the concrete Figure 6 two-wire action. -/
theorem dWord_action (a b : ZMod d) (v : Wires (ZMod d) (n + 2)) :
    Circuit.wireAction d (dWord a b 0 1 (zero_ne_one n)) v =
      Fin.cons (dAction a b (v 0, v 1)).1
        (Fin.cons (dAction a b (v 0, v 1)).2 (Fin.tail (Fin.tail v))) := by
  by_cases ha : a = 0
  · subst a
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [dWord, Circuit.wireAction_append, Equiv.swap_apply_def, dAction_zero, sub_eq_add_neg]
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp [dWord, Circuit.wireAction_append, Equiv.swap_apply_def, dAction_zero, sub_eq_add_neg]
      · simp [dWord, Circuit.wireAction_append, Equiv.swap_apply_def, dAction_zero, Fin.tail]
  · funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [dWord, ha, Circuit.wireAction_append, Equiv.swap_apply_def, dAction_nonzero a b ha]
      constructor <;> ring
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp [dWord, ha, Circuit.wireAction_append, Equiv.swap_apply_def, dAction_nonzero a b ha]
        field_simp
        ring
      · simp [dWord, ha, Circuit.wireAction_append, Equiv.swap_apply_def, dAction_nonzero a b ha,
          Fin.tail]

/-- Elaboration follows the A/B grammar, preserving every idle wire. -/
def ZNormal.toWord : {n : ℕ} → ZNormal (ZMod d) n → Circuit.Word n
  | _, .start A => A.toWord 0
  | _, .step a b N => bWord a b 0 1 (zero_ne_one _) ++
      Circuit.relabel (Circuit.shiftEmbedding _) N.toWord

/-- Elaboration follows the downward D sweep and terminal E. -/
def XNormal.toWord : {n : ℕ} → XNormal (ZMod d) n → Circuit.Word n
  | _, .finish c => eWord c 0
  | _, .step a b N => Circuit.relabel (Circuit.shiftEmbedding _) N.toWord ++
      dWord a b 0 1 (zero_ne_one _)

/-- The literal recursive normal form, fully expanded into the primitive alphabet. -/
def SymplecticNormalForm.toWord : {n : ℕ} → SymplecticNormalForm (ZMod d) n → Circuit.Word n
  | 0, .empty => []
  | _ + 1, .step Z X N => Circuit.relabel (Circuit.initialEmbedding _) N.toWord ++ X.toWord ++ Z.toWord

/-- The expanded A/B sweep realizes the proved Z-normal exponent action. -/
theorem ZNormal.toWord_action {n : ℕ} (N : ZNormal (ZMod d) n) (v : Wires (ZMod d) n) :
    Circuit.wireAction d N.toWord v = N.action v := by
  induction N with
  | start A =>
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;>
      simp [ZNormal.toWord, ABox.toWord_action, ZNormal.action, Fin.tail]
  | step a b N ih =>
    simp only [ZNormal.toWord, Circuit.wireAction_append, bWord_action,
      Circuit.wireAction_relabel_shift, ih, Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
    rfl

/-- The expanded D/E sweep realizes the proved X-normal exponent action. -/
theorem XNormal.toWord_action {n : ℕ} (N : XNormal (ZMod d) n) (v : Wires (ZMod d) n) :
    Circuit.wireAction d N.toWord v = N.action v := by
  induction N with
  | finish c =>
    funext k
    fin_cases k
    simp [XNormal.toWord, eWord_action, XNormal.action]
  | step a b N ih =>
    simp only [XNormal.toWord, Circuit.wireAction_append, dWord_action,
      Circuit.wireAction_relabel_shift, ih, Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
    rfl

/-- The entire recursive normal grammar elaborates faithfully into primitive words. -/
theorem SymplecticNormalForm.toWord_action {n : ℕ} (N : SymplecticNormalForm (ZMod d) n)
    (v : Wires (ZMod d) n) :
    Circuit.wireAction d N.toWord v = N.equiv v := by
  induction N with
  | empty => rfl
  | step Z X N ih =>
    simp only [SymplecticNormalForm.toWord, Circuit.wireAction_append,
      Circuit.wireAction_relabel_initial, ZNormal.toWord_action, XNormal.toWord_action, ih,
      SymplecticNormalForm.equiv_step_apply, WireSymplectic.lift_apply]

/-- The compiler preserves the actual established phase-space symplectic action. -/
theorem SymplecticNormalForm.toWord_symplecticAction {n : ℕ}
    (N : SymplecticNormalForm (ZMod d) n) (v : PhaseSpace d n) :
    Circuit.symplecticAction d N.toWord v = (toPhaseSymplectic N.equiv).val v := by
  apply (wiresCoordinates d n).symm.injective
  have h := N.toWord_action ((wiresCoordinates d n).symm v)
  change (wiresCoordinates d n).symm
    (Circuit.symplecticAction d N.toWord (wiresCoordinates d n ((wiresCoordinates d n).symm v))) = _ at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- Every symplectic map is represented by an actual word over the primitive
alphabet, via the literal normal-form compiler. -/
theorem exists_word_symplecticAction (F : symplecticGroup d n) :
    ∃ w : Circuit.Word n, ∀ v : PhaseSpace d n, Circuit.symplecticAction d w v = F.val v := by
  obtain ⟨N, hN, _⟩ := SymplecticNormalForm.existsUnique_equiv (fromPhaseSymplectic F)
  refine ⟨N.toWord, ?_⟩
  intro v
  rw [N.toWord_symplecticAction, hN]
  have hF := wireSymplecticEquiv.right_inv F
  exact congrArg (fun G : symplecticGroup d n => G.val v) hF

end QuditClifford.NormalBoxes
