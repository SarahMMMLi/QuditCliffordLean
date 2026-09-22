import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Circuit words and contextual rewriting

This file formalizes the distinction in Definitions 2.29–2.31 between a circuit,
its interpretation, and derivability using a specified collection of relations.
The alphabet can be the gates on any fixed number of wires. This is generic
infrastructure: no completeness assumption for Figure 1 is made here.
-/

namespace QuditClifford
namespace Presentation

variable {α : Type*}

/-- A circuit on a fixed collection of wires is a word in a gate alphabet. -/
abbrev Word (α : Type*) := List α

/-- Contextual, reflexive, symmetric, transitive closure of the given relations.
There is deliberately no constructor that turns semantic equality into a rewrite. -/
inductive Derives (R : Word α → Word α → Prop) : Word α → Word α → Prop
  | refl (w) : Derives R w w
  | rule {u v} : R u v → Derives R u v
  | symm {u v} : Derives R u v → Derives R v u
  | trans {u v w} : Derives R u v → Derives R v w → Derives R u w
  | context (l r) {u v} : Derives R u v → Derives R (l ++ u ++ r) (l ++ v ++ r)

namespace Derives

variable {R : Word α → Word α → Prop}

 theorem append_right {u v : Word α} (h : Derives R u v) (r : Word α) :
    Derives R (u ++ r) (v ++ r) := by
  simpa using h.context [] r

 theorem append_left {u v : Word α} (h : Derives R u v) (l : Word α) :
    Derives R (l ++ u) (l ++ v) := by
  simpa using h.context l []

 theorem append {u v u' v' : Word α} (h : Derives R u v) (h' : Derives R u' v') :
    Derives R (u ++ u') (v ++ v') :=
  (h.append_right u').trans (h'.append_left v)

 theorem mono {S : Word α → Word α → Prop}
    (hRS : ∀ u v, R u v → Derives S u v) {u v} (h : Derives R u v) :
    Derives S u v := by
  induction h with
  | refl w => exact .refl w
  | rule h => exact hRS _ _ h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih => exact ih.context l r

end Derives

/-- The quotient uses syntactic rewrites, not the equality of denotations. -/
def rewriteSetoid (R : Word α → Word α → Prop) : Setoid (Word α) where
  r := Derives R
  iseqv := ⟨Derives.refl, Derives.symm, Derives.trans⟩

variable {M : Type*} [Monoid M]

/-- Matrix-order interpretation: the leftmost letter is the leftmost factor.
For diagrams drawn in temporal order, reverse the gate list before interpreting. -/
def eval (interpret : α → M) (w : Word α) : M := (w.map interpret).prod

@[simp] theorem eval_nil (interpret : α → M) : eval interpret [] = 1 := rfl

@[simp] theorem eval_cons (interpret : α → M) (a : α) (w : Word α) :
    eval interpret (a :: w) = interpret a * eval interpret w := rfl

@[simp] theorem eval_append (interpret : α → M) (u v : Word α) :
    eval interpret (u ++ v) = eval interpret u * eval interpret v := by
  simp [eval]

/-- Definition 2.31: soundness of the generating equations. -/
def Sound (R : Word α → Word α → Prop) (interpret : α → M) : Prop :=
  ∀ u v, R u v → eval interpret u = eval interpret v

/-- Definition 2.31: semantic equality implies derivability. -/
def Complete (R : Word α → Word α → Prop) (interpret : α → M) : Prop :=
  ∀ u v, eval interpret u = eval interpret v → Derives R u v

/-- Sound local equations remain sound in every sequential context. -/
theorem sound_derives {R : Word α → Word α → Prop} {interpret : α → M}
    (hR : Sound R interpret) {u v} (h : Derives R u v) :
    eval interpret u = eval interpret v := by
  induction h with
  | refl w => rfl
  | rule h => exact hR _ _ h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih => simp only [eval_append, ih]

/-- The normalization strategy used in Sections 3–4. Both normalization and
uniqueness of normal forms are hypotheses here, not claims about Figure 1. -/
theorem complete_of_normal_forms {R : Word α → Word α → Prop}
    {interpret : α → M} (normal : Word α → Word α)
    (reduces : ∀ w, Derives R w (normal w))
    (unique : ∀ u v, eval interpret u = eval interpret v → normal u = normal v) :
    Complete R interpret := by
  intro u v h
  exact (reduces u).trans ((unique u v h) ▸ (reduces v).symm)

/-- Soundness and completeness are separate obligations. -/
theorem derives_iff_eval_eq {R : Word α → Word α → Prop} {interpret : α → M}
    (hs : Sound R interpret) (hc : Complete R interpret) (u v : Word α) :
    Derives R u v ↔ eval interpret u = eval interpret v :=
  ⟨sound_derives hs, hc u v⟩

section ExactLifting

variable {G Q K C : Type*} [Group G] [Group Q] [Group K] [Group C]

/-- The group-theoretic final step of exact completeness. `K` is the group of
circuits modulo the proposed rewrites, `e` is their exact interpretation, `q`
forgets the central scalar, and `s` represents scalar words.

The difficult lifting obligation is explicit: every word whose interpretation
is trivial after forgetting scalars must already be derivably a scalar (`lifts`).
Faithfulness of scalar interpretation then rules out a residual exact kernel.
This lemma does NOT establish `lifts` for the paper's rules. -/
theorem exact_injective_of_projective_lifting
    (e : K →* G) (q : G →* Q) (s : C →* K)
    (scalar_faithful : Function.Injective (e.comp s))
    (lifts : ∀ k, q (e k) = 1 → ∃ c, s c = k) :
    Function.Injective e := by
  apply (MonoidHom.ker_eq_bot_iff e).mp
  apply bot_unique
  intro k hk
  have hek : e k = 1 := hk
  obtain ⟨c, rfl⟩ := lifts k (by rw [hek, map_one])
  have hc : c = 1 := scalar_faithful (by simpa using hek)
  simp [hc]

/-- An equivalent useful form: it is enough that the projective kernel lies in
the represented scalars and that exact scalar equality is faithfully detected. -/
theorem exact_injective_of_kernel_le_range
    (e : K →* G) (q : G →* Q) (s : C →* K)
    (scalar_faithful : Function.Injective (e.comp s))
    (hker : (q.comp e).ker ≤ s.range) : Function.Injective e := by
  apply exact_injective_of_projective_lifting e q s scalar_faithful
  intro k hk
  exact hker hk

end ExactLifting
end Presentation
end QuditClifford
