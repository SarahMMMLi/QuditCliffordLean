import QuditClifford.AdjacentXNormalPushCZ
import QuditClifford.NormalSweepSyntax
import QuditClifford.AdjacentPresentedSymplectic

/-!
# Full X-normal sweep of the typed residual grammar

Each allowed intermediate gate is pushed by its proved restricted S/H/CZ
case, or explicitly erased when it is scalar. Induction composes these
local pushes into a derivation for every typed residual word.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Every gate emitted by a Z sweep passes through an X-normal sweep. -/
theorem XNormal.adjacentSymplecticDerives_pushGate
    (N : XNormal (ZMod d) (n+1)) (a : ZSweepGate n) :
    ∃ (r : AdjacentWord n) (N' : XNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [a.toGate])
        (relabel (initialEmbedding n) r.toWord ++ N'.toWord) := by
  cases a with
  | scalar =>
    refine ⟨[], N, ?_⟩
    simpa only [ZSweepGate.toGate, scalar, List.replicate_one, AdjacentWord.toWord_nil,
      relabel_nil, List.nil_append, List.append_nil] using
      (adjacentSymplecticDerives_scalar (n := n+1) g 1).append_left N.toWord
  | H i => exact N.adjacentSymplecticDerives_pushH g i
  | S i =>
    obtain ⟨r, N', h⟩ := N.adjacentDerives_pushS g i
    exact ⟨r, N', adjacentDerives_symplectic g h⟩
  | CZ i => exact N.adjacentSymplecticDerives_pushCZ g i

/-- An entire Z-sweep residual passes through X normalization, producing a
literal adjacent circuit on one fewer wire and a new X-normal label. -/
theorem XNormal.adjacentSymplecticDerives_pushWord
    (N : XNormal (ZMod d) (n+1)) (w : ZSweepWord n) :
    ∃ (r : AdjacentWord n) (N' : XNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ ZSweepWord.toWord w)
        (relabel (initialEmbedding n) r.toWord ++ N'.toWord) := by
  induction w generalizing N with
  | nil =>
    refine ⟨[], N, ?_⟩
    simpa only [ZSweepWord.toWord_nil, AdjacentWord.toWord_nil, relabel_nil,
      List.append_nil, List.nil_append] using
      (show AdjacentSymplecticDerives g N.toWord N.toWord from .refl _)
  | cons a w ih =>
    obtain ⟨r₀, N₀, h₀⟩ := N.adjacentSymplecticDerives_pushGate g a
    obtain ⟨r₁, N₁, h₁⟩ := ih N₀
    refine ⟨r₀ ++ r₁, N₁, ?_⟩
    have hs := h₀.append_right (ZSweepWord.toWord w)
    have ht := h₁.append_left (relabel (initialEmbedding n) r₀.toWord)
    simp only [List.append_assoc] at hs ht
    simpa only [ZSweepWord.toWord_cons, AdjacentWord.toWord_append, relabel_append,
      List.append_assoc, List.singleton_append] using hs.trans ht

end QuditClifford.NormalBoxes
