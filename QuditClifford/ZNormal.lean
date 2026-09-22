import QuditClifford.NormalLayers

/-!
# The paper's concrete arbitrary-wire Z-normal circuits

The grammar below contains exactly one A box at its last active wire, B boxes
connecting each preceding adjacent pair of wires, and idle wires after the A.
Its action uses the concrete Figure 6 boxes from `NormalLayers`, with temporal
order matching Definition 3.1 and Appendix E. All results are exponent-level
statements. No claim about derivability from the rewrite rules is made here.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
universe u
variable {K : Type u} [Field K]

/-- A wire-by-wire list of `(z,x)` Pauli exponents. -/
abbrev Wires (K : Type*) (n : ℕ) := Fin n → Vector K

@[simp] theorem cons_zero (n : ℕ) :
    Fin.cons (0 : Vector K) (0 : Wires K n) = (0 : Wires K (n + 1)) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- `Z` on the first wire and zero on every subsequent wire. -/
def headZ (n : ℕ) : Wires K (n + 1) := Fin.cons zVector 0

/-- The standard symplectic form, expressed wire by wire. -/
def wiresBracket {n : ℕ} (v w : Wires K n) : K := ∑ i, bracket (v i) (w i)

@[simp] theorem wiresBracket_cons {n : ℕ} (v w : Vector K) (vs ws : Wires K n) :
    wiresBracket (Fin.cons v vs) (Fin.cons w ws) = bracket v w + wiresBracket vs ws := by
  simp [wiresBracket, Fin.sum_univ_succ]

theorem wiresBracket_expand {n : ℕ} (v w : Wires K (n + 1)) :
    wiresBracket v w = bracket (v 0) (w 0) + wiresBracket (Fin.tail v) (Fin.tail w) := by
  simp [wiresBracket, Fin.sum_univ_succ, Fin.tail]

@[simp] theorem wiresBracket_zero_left {n : ℕ} (v : Wires K n) :
    wiresBracket 0 v = 0 := by simp [wiresBracket, bracket]

@[simp] theorem wiresBracket_zero_right {n : ℕ} (v : Wires K n) :
    wiresBracket v 0 = 0 := by simp [wiresBracket, bracket]

@[simp] theorem wiresBracket_headZ {n : ℕ} (v : Wires K (n + 1)) :
    wiresBracket (headZ n) v = (v 0).2 := by
  rw [wiresBracket_expand]
  simp [headZ]

/-- An A box on the first wire, or one B box after a Z-normal tail.
`start` retains `n` idle wires following its A box. -/
inductive ZNormal (K : Type u) [Field K] : ℕ → Type u
  | start {n : ℕ} (A : ABox K) : ZNormal K (n + 1)
  | step {n : ℕ} (a b : K) (tail : ZNormal K (n + 1)) : ZNormal K (n + 2)

namespace ZNormal

/-- Read the unique input exponents from the A/B labels, as in Appendix E. -/
def input : {n : ℕ} → ZNormal K n → Wires K n
  | _, .start A => Fin.cons A.input 0
  | _, .step a b N => Fin.cons (b, a) N.input

/-- Execute the actual A/B sweep, with idle wires unchanged. -/
def action : {n : ℕ} → ZNormal K n → Wires K n → Wires K n
  | _, .start A, v => Fin.cons (A.action (v 0)) (Fin.tail v)
  | _, .step a b N, v =>
      let w := N.action (Fin.tail v)
      let p := bAction a b (v 0, w 0)
      Fin.cons p.1 (Fin.cons p.2 (Fin.tail w))

@[simp] theorem action_input : {n : ℕ} → (N : ZNormal K (n + 1)) →
    N.action N.input = headZ n
  | _, .start A => by simp [action, input, headZ, ABox.action_input]
  | _ + 1, .step a b N => by
    rw [show (step a b N).action (step a b N).input =
      Fin.cons (bAction a b ((b, a), (N.action N.input) 0)).1
        (Fin.cons (bAction a b ((b, a), (N.action N.input) 0)).2
          (Fin.tail (N.action N.input))) by simp [action, input]]
    rw [action_input N]
    simp [headZ, bAction_input]

@[simp] theorem input_ne_zero : {n : ℕ} → (N : ZNormal K (n + 1)) → N.input ≠ 0
  | _, .start A => by
    intro h
    have hh := congrFun h 0
    change A.input = 0 at hh
    exact A.input_ne_zero hh
  | _ + 1, .step a b N => by
    intro h
    have hh := congrArg Fin.tail h
    simp only [input, Fin.tail_cons] at hh
    exact input_ne_zero N hh

omit [Field K] in
theorem wires_ext {n : ℕ} {v w : Wires K (n + 1)}
    (hhead : v 0 = w 0) (htail : Fin.tail v = Fin.tail w) : v = w := by
  funext i
  cases i using Fin.cases
  · exact hhead
  · exact congrFun htail _

/-- Every concrete Z-normal action is injective. -/
theorem action_injective {n : ℕ} (N : ZNormal K n) : Function.Injective N.action := by
  induction N with
  | start A =>
    intro v w h
    have hh := congrFun h 0
    have ht := congrArg Fin.tail h
    have hhead : v 0 = w 0 := A.action_injective (by simpa [action] using hh)
    have htail : Fin.tail v = Fin.tail w := by simpa [action] using ht
    exact wires_ext hhead htail
  | @step n a b N ih =>
    intro v w h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    have ht := congrArg (fun u => Fin.tail (Fin.tail u)) h
    have hp : bAction a b (v 0, N.action (Fin.tail v) 0) =
        bAction a b (w 0, N.action (Fin.tail w) 0) :=
      Prod.ext (by simpa [action] using h₀) (by simpa [action] using h₁)
    have hpair := bAction_injective a b hp
    have hhead : v 0 = w 0 := congrArg Prod.fst hpair
    have hmid : N.action (Fin.tail v) 0 = N.action (Fin.tail w) 0 :=
      congrArg Prod.snd hpair
    have hlast : Fin.tail (N.action (Fin.tail v)) = Fin.tail (N.action (Fin.tail w)) := by
      simpa [action] using ht
    have hntail : N.action (Fin.tail v) = N.action (Fin.tail w) := by
      exact wires_ext hmid hlast
    have htail := ih hntail
    exact wires_ext hhead htail

/-- Every Z-normal word has exactly its label-read input as preimage of `Z`. -/
theorem action_eq_headZ_iff {n : ℕ} (N : ZNormal K (n + 1)) (v : Wires K (n + 1)) :
    N.action v = headZ n ↔ v = N.input := by
  rw [← N.action_input]
  exact ⟨fun h => N.action_injective h, congrArg N.action⟩

/-- The concrete whole Z sweep preserves the symplectic form. -/
theorem preserves {n : ℕ} (N : ZNormal K n) (v w : Wires K n) :
    wiresBracket (N.action v) (N.action w) = wiresBracket v w := by
  induction N with
  | start A =>
    simp only [action, wiresBracket_cons, ABox.preserves]
    exact (wiresBracket_expand v w).symm
  | @step n a b N ih =>
    simp only [action, wiresBracket_cons]
    rw [← add_assoc]
    change twoBracket (bAction a b (v 0, N.action (Fin.tail v) 0))
        (bAction a b (w 0, N.action (Fin.tail w) 0)) + _ = _
    rw [bAction_preserves]
    dsimp only [twoBracket]
    rw [add_assoc, ← wiresBracket_expand, ih]
    exact (wiresBracket_expand v w).symm

/-- The syntax contains no duplicate words with the same label-read input. -/
theorem input_injective {n : ℕ} : Function.Injective (input : ZNormal K n → Wires K n) := by
  intro N M h
  induction N with
  | start A =>
    cases M with
    | start B =>
      have hh := congrFun h 0
      have hab : A.input = B.input := by simpa [input] using hh
      have hAB : A = B := ABox.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
      exact congrArg ZNormal.start hAB
    | step a b M =>
      exfalso
      apply M.input_ne_zero
      have ht := congrArg Fin.tail h
      simpa [input] using ht.symm
  | @step n a b N ih =>
    cases M with
    | start B =>
      exfalso
      apply N.input_ne_zero
      have ht := congrArg Fin.tail h
      simp only [input, Fin.tail_cons] at ht
      exact ht
    | step c d M =>
      have hh : (b, a) = (d, c) := by simpa [input] using congrFun h 0
      have ht : N.input = M.input := by simpa [input] using congrArg Fin.tail h
      have hNM := ih ht
      cases hNM
      have ha := congrArg Prod.snd hh
      have hb := congrArg Prod.fst hh
      cases ha
      cases hb
      rfl

/-- The last-nonzero-wire construction from Appendix E. -/
theorem exists_input {n : ℕ} (v : Wires K n) (hv : v ≠ 0) :
    ∃ N : ZNormal K n, N.input = v := by
  induction n with
  | zero =>
    exfalso
    apply hv
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    classical
    by_cases ht : Fin.tail v = 0
    · have hhead : v 0 ≠ 0 := by
        intro hh
        apply hv
        exact wires_ext hh ht
      let A : ABox K := ⟨(v 0).2, (v 0).1, hhead⟩
      refine ⟨.start A, ?_⟩
      apply wires_ext
      · rfl
      · simpa [input] using ht.symm
    · cases n with
      | zero =>
        exfalso
        apply ht
        funext i
        exact Fin.elim0 i
      | succ n =>
        obtain ⟨N, hN⟩ := ih (Fin.tail v) ht
        refine ⟨.step (v 0).2 (v 0).1 N, ?_⟩
        apply wires_ext
        · rfl
        · simpa [input] using hN

/-- Lemma 3.4 at the exponent level, for the actual A/B circuit grammar:
every nonzero Pauli vector has exactly one concrete Z-normal word sending it
to Z on the first wire. -/
theorem existsUnique_normalizer {n : ℕ} (v : Wires K (n + 1)) (hv : v ≠ 0) :
    ∃! N : ZNormal K (n + 1), N.action v = headZ n := by
  obtain ⟨N, hN⟩ := exists_input v hv
  refine ⟨N, ?_, ?_⟩
  · exact (N.action_eq_headZ_iff v).mpr hN.symm
  · intro M hM
    apply input_injective
    rw [← (M.action_eq_headZ_iff v).mp hM, hN]

end ZNormal
end QuditClifford.NormalBoxes
