import QuditClifford.SymplecticOneWire
import QuditClifford.PauliLifting

/-!
# One-qudit normalization in the syntactic symplectic presentation

The words here are the literal E-A box normal forms. Normal-form uniqueness
uses their concrete exponent action; normalization itself uses only the
syntactic box transitions.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit

variable {d : ℕ} [Fact d.Prime] [NeZero d]

/-- The matrix-order word for the paper's temporal A;E normal form. -/
def OneQuditNormal.toWord (N : OneQuditNormal (ZMod d)) : Word 1 :=
  eWord N.last 0 ++ N.first.toWord 0

omit [NeZero d] in
theorem OneQuditNormal.toWord_action (N : OneQuditNormal (ZMod d))
    (v : Wires (ZMod d) 1) : wireAction d N.toWord v 0 = N.action (v 0) := by
  simp [OneQuditNormal.toWord, wireAction_append, eWord_action,
    ABox.toWord_action, OneQuditNormal.action_apply]

/-- Distinct one-qudit box labels have distinct linear actions. -/
theorem OneQuditNormal.action_injective :
    Function.Injective (OneQuditNormal.action : OneQuditNormal (ZMod d) → _) := by
  intro N M he
  have hinput : N.first.input = M.first.input := by
    apply (M.action_eq_z_iff N.first.input).mp
    rw [← he]
    exact N.action_first_input
  have hfirst : N.first = M.first :=
    ABox.ext (congrArg Prod.snd hinput) (congrArg Prod.fst hinput)
  apply OneQuditNormal.ext hfirst
  have hsurj : Function.Surjective N.first.action :=
    Finite.surjective_of_injective N.first.action_injective
  obtain ⟨v, hv⟩ := hsurj xVector
  have hl := LinearMap.congr_fun he v
  simp only [OneQuditNormal.action_apply, ← hfirst, hv, eAction_apply, xVector,
    mul_one, zero_sub] at hl
  exact neg_injective (congrArg Prod.fst hl)

/-- Concrete exponent equality uniquely determines an E-A word's box labels. -/
theorem OneQuditNormal.eq_of_toWord_symplecticAction_eq
    (N M : OneQuditNormal (ZMod d))
    (h : ∀ p, symplecticAction d N.toWord p = symplecticAction d M.toWord p) : N = M := by
  apply OneQuditNormal.action_injective
  apply LinearMap.ext
  intro v
  have he := congrArg (fun p => (wiresCoordinates d 1).symm p 0)
    (h (wiresCoordinates d 1 (fun _ => v)))
  change wireAction d N.toWord (fun _ => v) 0 = wireAction d M.toWord (fun _ => v) 0 at he
  simpa only [OneQuditNormal.toWord_action] using he

end QuditClifford.NormalBoxes

namespace QuditClifford.Circuit
open NormalBoxes
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private def identityOneQuditNormal : OneQuditNormal (ZMod d) :=
  ⟨⟨0, 1, by simp⟩, 0⟩

set_option linter.unusedSectionVars false in
private theorem identityOneQuditNormal_classWord :
    symplecticClassWord g (identityOneQuditNormal (d := d)).toWord = 1 := by
  have hm := (symplecticClassWord_eq_iff_derives g _ _).mpr
    (derives_symplectic g (derives_multiplier_one g (0 : Fin 1)))
  simpa [identityOneQuditNormal, OneQuditNormal.toWord, eWord, ABox.toWord,
    Units.mk0_one] using hm

/-- Syntactic right-closure of the E-A forms follows from the two A-box transitions. -/
theorem exists_oneQuditNormal_of_box_steps
    (hH : ∀ A : ABox (ZMod d), ∃ (c : ZMod d) (A' : ABox (ZMod d)), SymplecticDerives g
      (A.toWord (0 : Fin 1) ++ [.H 0]) (Sexp 0 c ++ A'.toWord 0))
    (hS : ∀ A : ABox (ZMod d), ∃ (c : ZMod d) (A' : ABox (ZMod d)), SymplecticDerives g
      (A.toWord (0 : Fin 1) ++ [.S 0]) (Sexp 0 c ++ A'.toWord 0))
    (w : Word 1) : ∃ N : OneQuditNormal (ZMod d),
      symplecticClassWord g w = symplecticClassWord g N.toWord := by
  induction w using List.reverseRecOn with
  | nil =>
      exact ⟨identityOneQuditNormal, (identityOneQuditNormal_classWord g).symm⟩
  | append_singleton w a ih =>
      obtain ⟨N, hN⟩ := ih
      have step {a : Gate 1} (hs : ∃ (c : ZMod d) (A' : ABox (ZMod d)), SymplecticDerives g
          (N.first.toWord 0 ++ [a]) (Sexp 0 c ++ A'.toWord 0)) :
          ∃ M : OneQuditNormal (ZMod d),
            symplecticClassWord g (w ++ [a]) = symplecticClassWord g M.toWord := by
        obtain ⟨c, A, hc⟩ := hs
        refine ⟨⟨A, N.last-c⟩, ?_⟩
        have he := (symplecticClassWord_eq_iff_derives g _ _).mpr hc
        simp only [symplecticClassWord_append] at he
        simp only [symplecticClassWord_append, hN, OneQuditNormal.toWord, eWord]
        rw [mul_assoc, he, ← mul_assoc, ← symplecticClassWord_Sexp_add]
        congr 2
        ring_nf
      cases a with
      | scalar =>
          refine ⟨N, ?_⟩
          have hs : symplecticClassWord (n := 1) g [.scalar] = 1 := by
            simpa [scalar] using symplecticClassWord_scalar (n := 1) g 1
          rw [symplecticClassWord_append, hs, mul_one, hN]
      | H i =>
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact step (hH N.first)
      | S i =>
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact step (hS N.first)
      | CZ i j hij => exact (hij (Subsingleton.elim _ _)).elim

/-- Once A-box pushing is proved, one-qudit erased completeness follows by
actual word normalization and the proved uniqueness of concrete E-A labels. -/
theorem symplecticErasureComplete_one_of_box_steps
    (hH : ∀ A : ABox (ZMod d), ∃ (c : ZMod d) (A' : ABox (ZMod d)), SymplecticDerives g
      (A.toWord (0 : Fin 1) ++ [.H 0]) (Sexp 0 c ++ A'.toWord 0))
    (hS : ∀ A : ABox (ZMod d), ∃ (c : ZMod d) (A' : ABox (ZMod d)), SymplecticDerives g
      (A.toWord (0 : Fin 1) ++ [.S 0]) (Sexp 0 c ++ A'.toWord 0)) :
    SymplecticErasureComplete (n := 1) g := by
  intro u v huv
  obtain ⟨N, hN⟩ := exists_oneQuditNormal_of_box_steps g hH hS u
  obtain ⟨M, hM⟩ := exists_oneQuditNormal_of_box_steps g hH hS v
  have hNM : N = M := by
    apply OneQuditNormal.eq_of_toWord_symplecticAction_eq
    intro p
    have hn := congrArg (fun q => (presentedSymplecticInterpret (Fact.out : Odd d) g q).val p) hN
    have hm := congrArg (fun q => (presentedSymplecticInterpret (Fact.out : Odd d) g q).val p) hM
    simp only [presentedSymplecticInterpret_apply] at hn hm
    exact hn.symm.trans ((huv p).trans hm)
  apply (symplecticClassWord_eq_iff_derives g u v).mp
  exact hN.trans (hNM ▸ hM.symm)

/-- Every one-qudit circuit is syntactically reducible to a concrete E-A form
after the explicit scalar and Pauli deletions. -/
theorem exists_oneQuditNormal_derives (w : Word 1) :
    ∃ N : OneQuditNormal (ZMod d), SymplecticDerives g w N.toWord := by
  obtain ⟨N, hN⟩ := exists_oneQuditNormal_of_box_steps g
    (fun A => symplectic_A_H g A 0) (fun A => symplectic_A_S g A 0) w
  exact ⟨N, (symplecticClassWord_eq_iff_derives g _ _).mp hN⟩

/-- The one-qudit box normal form is unique under the actual erased rewrite relation. -/
theorem existsUnique_oneQuditNormal_derives (w : Word 1) :
    ∃! N : OneQuditNormal (ZMod d), SymplecticDerives g w N.toWord := by
  obtain ⟨N, hN⟩ := exists_oneQuditNormal_derives g w
  refine ⟨N, hN, ?_⟩
  intro M hM
  apply OneQuditNormal.eq_of_toWord_symplecticAction_eq
  have he := (symplecticClassWord_eq_iff_derives g _ _).mpr (hM.symm.trans hN)
  intro p
  simpa only [presentedSymplecticInterpret_apply] using
    congrArg (fun q => (presentedSymplecticInterpret (Fact.out : Odd d) g q).val p) he

/-- Completeness of the explicit symplectic erasure for a single qudit. -/
theorem symplecticErasureComplete_one : SymplecticErasureComplete (n := 1) g :=
  symplecticErasureComplete_one_of_box_steps g
    (fun A => symplectic_A_H g A 0) (fun A => symplectic_A_S g A 0)

/-- The full exact Figure 1 presentation is complete for one qudit, including
the selected scalar convention `-ω` and the actual expanded Pauli words. -/
theorem figure1Complete_one : Figure1Complete (n := 1) g :=
  figure1Complete_of_symplecticErasureComplete g (symplecticErasureComplete_one g)

/-- At arity one, exact matrix equality is equivalent to Figure 1 derivability. -/
theorem derives_iff_denote_eq_one (u v : Word 1) :
    Derives g u v ↔ denote d u = denote d v :=
  ⟨figure1_sound (Fact.out : Odd d) g u v, figure1Complete_one g u v⟩

end QuditClifford.Circuit
