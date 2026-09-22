import QuditClifford.ZNormal

/-!
# The concrete arbitrary-wire X-normal circuits

The D boxes sweep down all adjacent wire pairs, followed by E on the last wire.
This is the literal grammar in Definition 3.1 and Appendix E. The proofs below
establish Lemmas 3.5 and 3.6 on exponent vectors using concrete Figure 6 words.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
universe u
variable {K : Type u} [Field K]

/-- A specified Pauli exponent on the last wire, with zero preceding wires. -/
def lastVector (v : Vector K) : (n : ℕ) → Wires K (n + 1)
  | 0 => Fin.cons v 0
  | n + 1 => Fin.cons 0 (lastVector v n)

/-- Exactly `n` D boxes followed by one E box on `n+1` wires. -/
inductive XNormal (K : Type u) [Field K] : ℕ → Type u
  | finish (c : K) : XNormal K 1
  | step {n : ℕ} (a b : K) (tail : XNormal K (n + 1)) : XNormal K (n + 2)

namespace XNormal

/-- The phase-shear label of the terminal E box. -/
def phase : {n : ℕ} → XNormal K n → K
  | _, .finish c => c
  | _, .step _ _ N => N.phase

/-- Read the input exponents from the D labels and terminal E label. -/
def input : {n : ℕ} → XNormal K n → Wires K n
  | _, .finish c => Fin.cons (c, 1) 0
  | _, .step a b N => Fin.cons (N.input 0) (Fin.cons (b, a) (Fin.tail N.input))

/-- Execute each concrete D box in order and the final E box. -/
def action : {n : ℕ} → XNormal K n → Wires K n → Wires K n
  | _, .finish c, v => Fin.cons (eAction c (v 0)) 0
  | _, .step a b N, v =>
      let p := dAction a b (v 0, v 1)
      Fin.cons p.1 (N.action (Fin.cons p.2 (Fin.tail (Fin.tail v))))

@[simp] theorem input_head : {n : ℕ} → (N : XNormal K (n + 1)) →
    N.input 0 = (N.phase, 1)
  | 0, .finish c => rfl
  | _ + 1, .step a b N => by simpa [input, phase] using input_head N

@[simp] theorem action_input : {n : ℕ} → (N : XNormal K (n + 1)) →
    N.action N.input = lastVector xVector n
  | 0, .finish c => by simp [action, input, lastVector, eAction_input, xVector]
  | _ + 1, .step a b N => by
    simp only [action, input, Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.tail_cons,
      N.input_head, dAction_input]
    rw [show Fin.cons (N.phase, 1) (Fin.tail N.input) = N.input by
      rw [← N.input_head, Fin.cons_self_tail]]
    exact congrArg (Fin.cons 0) (action_input N)

/-- Lemma 3.6: every concrete X-normal circuit carries the first Z to the last wire. -/
@[simp] theorem action_headZ : {n : ℕ} → (N : XNormal K (n + 1)) →
    N.action (headZ n) = lastVector zVector n
  | 0, .finish c => by
    simp only [action, headZ, Fin.cons_zero, eAction_z, lastVector]
  | n + 1, .step a b N => by
    simp only [action, headZ, Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Pi.zero_apply,
      dAction_upper_z, Fin.tail_cons]
    change Fin.cons (0 : Vector K) (N.action (headZ n)) =
      (Fin.cons (0 : Vector K) (lastVector (K := K) zVector n) : Wires K (n + 2))
    rw [action_headZ N]

theorem action_injective {n : ℕ} (N : XNormal K n) : Function.Injective N.action := by
  induction N with
  | finish c =>
    intro v w h
    have hE : eAction c (v 0) = eAction c (w 0) := by
      simpa [action] using congrFun h 0
    have hhead : v 0 = w 0 := by
      apply bracket_ext
      intro u
      rw [← eAction_preserves c (v 0) u, ← eAction_preserves c (w 0) u, hE]
    apply ZNormal.wires_ext hhead
    funext i
    exact Fin.elim0 i
  | @step n a b N ih =>
    intro v w h
    have ht := congrArg Fin.tail h
    simp only [action, Fin.tail_cons] at ht
    have hn := ih ht
    have hp : dAction a b (v 0, v 1) = dAction a b (w 0, w 1) := by
      apply Prod.ext
      · simpa only [action, Fin.cons_zero] using congrFun h 0
      · simpa only [Fin.cons_zero] using congrFun hn 0
    have hpair := dAction_injective a b hp
    apply ZNormal.wires_ext (congrArg Prod.fst hpair)
    apply ZNormal.wires_ext
    · exact congrArg Prod.snd hpair
    · simpa only [Fin.tail_cons] using congrArg Fin.tail hn

theorem action_eq_lastX_iff {n : ℕ} (N : XNormal K (n + 1)) (v : Wires K (n + 1)) :
    N.action v = lastVector xVector n ↔ v = N.input := by
  rw [← N.action_input]
  exact ⟨fun h => N.action_injective h, congrArg N.action⟩

/-- Only the first Z has the required final Z image. -/
theorem action_eq_lastZ_iff {n : ℕ} (N : XNormal K (n + 1)) (v : Wires K (n + 1)) :
    N.action v = lastVector zVector n ↔ v = headZ n := by
  rw [← N.action_headZ]
  exact ⟨fun h => N.action_injective h, congrArg N.action⟩

/-- The complete D/E sweep preserves the symplectic form. -/
theorem preserves {n : ℕ} (N : XNormal K n) (v w : Wires K n) :
    wiresBracket (N.action v) (N.action w) = wiresBracket v w := by
  induction N with
  | finish c =>
    simp only [action, wiresBracket_cons, eAction_preserves, wiresBracket_zero_left, add_zero]
    simp [wiresBracket, Fin.sum_univ_one]
  | @step n a b N ih =>
    simp only [action, wiresBracket_cons, ih, wiresBracket_cons]
    rw [← add_assoc]
    change twoBracket (dAction a b (v 0, v 1)) (dAction a b (w 0, w 1)) + _ = _
    rw [dAction_preserves]
    dsimp only [twoBracket]
    rw [add_assoc]
    rw [wiresBracket_expand v w, wiresBracket_expand (Fin.tail v) (Fin.tail w)]
    rfl

/-- Different concrete D/E words have different label-read inputs. -/
theorem input_injective {n : ℕ} : Function.Injective (input : XNormal K n → Wires K n) := by
  intro N M h
  induction N with
  | finish c =>
    cases M with
    | finish d =>
      have hh : (c, (1 : K)) = (d, 1) := by simpa [input] using congrFun h 0
      exact congrArg XNormal.finish (congrArg Prod.fst hh)
  | @step n a b N ih =>
    cases M with
    | step c d M =>
      have hp : (b, a) = (d, c) := by simpa [input] using congrFun h 1
      have hhead : N.input 0 = M.input 0 := by simpa [input] using congrFun h 0
      have htail : Fin.tail N.input = Fin.tail M.input := by
        simpa [input] using congrArg (fun v => Fin.tail (Fin.tail v)) h
      have hNM := ih (ZNormal.wires_ext hhead htail)
      cases hNM
      have ha := congrArg Prod.snd hp
      have hb := congrArg Prod.fst hp
      cases ha
      cases hb
      rfl

/-- The downward-sweep construction from Appendix E. -/
theorem exists_input : {n : ℕ} → (v : Wires K (n + 1)) → (v 0).2 = 1 →
    ∃ N : XNormal K (n + 1), N.input = v
  | 0, v, hv => by
    refine ⟨.finish (v 0).1, ?_⟩
    apply ZNormal.wires_ext
    · exact Prod.ext rfl hv.symm
    · funext i
      exact Fin.elim0 i
  | n + 1, v, hv => by
    let w : Wires K (n + 1) := Fin.cons (v 0) (Fin.tail (Fin.tail v))
    obtain ⟨N, hN⟩ := exists_input w (by simpa [w] using hv)
    refine ⟨.step (v 1).2 (v 1).1 N, ?_⟩
    apply ZNormal.wires_ext
    · simpa [input, w] using congrFun hN 0
    · apply ZNormal.wires_ext
      · rfl
      · simpa [input, w] using congrArg Fin.tail hN

/-- Lemma 3.5 at the exponent level, for the actual D/E grammar. The
commutation hypothesis with the first Z is exactly `(v 0).2 = 1`. -/
theorem existsUnique_normalizer {n : ℕ} (v : Wires K (n + 1)) (hv : (v 0).2 = 1) :
    ∃! N : XNormal K (n + 1), N.action v = lastVector xVector n := by
  obtain ⟨N, hN⟩ := exists_input v hv
  refine ⟨N, (N.action_eq_lastX_iff v).mpr hN.symm, ?_⟩
  intro M hM
  apply input_injective
  rw [← (M.action_eq_lastX_iff v).mp hM, hN]

end XNormal
/-- Lemma 3.7 for the actual A/B and D/E circuit grammars: a symplectic
Pauli pair has a unique Z-normal/X-normal pair taking it to the last Z/X. -/
theorem existsUnique_pair_normalizer {n : ℕ} (p q : Wires K (n + 1))
    (hpq : wiresBracket p q = 1) :
    ∃! N : ZNormal K (n + 1) × XNormal K (n + 1),
      N.2.action (N.1.action p) = lastVector zVector n ∧
      N.2.action (N.1.action q) = lastVector xVector n := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hpq
  obtain ⟨Z, hZ, hZuniq⟩ := ZNormal.existsUnique_normalizer p hp
  have hq : (Z.action q 0).2 = 1 := by
    have h := Z.preserves p q
    rw [hZ, wiresBracket_headZ, hpq] at h
    exact h
  obtain ⟨X, hX, hXuniq⟩ := XNormal.existsUnique_normalizer (Z.action q) hq
  refine ⟨(Z, X), ⟨?_, hX⟩, ?_⟩
  · dsimp only
    rw [hZ, X.action_headZ]
  · intro M hM
    have hMZ := (M.2.action_eq_lastZ_iff (M.1.action p)).mp hM.1
    have hz : M.1 = Z := hZuniq M.1 hMZ
    have hx : M.2 = X := hXuniq M.2 (by simpa only [hz] using hM.2)
    exact Prod.ext hz hx

end QuditClifford.NormalBoxes
