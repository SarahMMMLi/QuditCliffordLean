import QuditClifford.AdjacentXNormalSweep
import QuditClifford.AdjacentNormalRewriteInduction

/-!
# Recursive normal-form closure from the two typed sweeps

The X sweep is already proved. This assembly isolates the concrete
Z-sweep interface, then proves recursive gate closure by induction on the
number of wires. Residual words are normalized on strictly fewer wires.
The Z-sweep premise is a derivation statement, not semantic equality or
completeness. `AdjacentCompleteness.lean` supplies the proved Z sweep.
-/

noncomputable section
namespace QuditClifford.Circuit
open NormalBoxes
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ)

/-- The precise Z-sweep gate-pushing interface: a typed intermediate residual
and another Z-normal form, related by restricted erased rewrites. -/
def AdjacentZNormalGateClosure : Prop :=
  ∀ n (N : ZNormal (ZMod d) (n+1)) (a : AdjacentGate (n+1)),
    ∃ (r : ZSweepWord n) (N' : ZNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [a.toGate]) (r.toWord ++ N'.toWord)

variable [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The proved X sweep and the concrete Z-sweep interface give full recursive
normal-form gate closure at every arity. -/
theorem adjacentNormalFormGateClosure_of_zSweep (hZ : AdjacentZNormalGateClosure g) :
    ∀ n, AdjacentNormalFormGateClosure (n := n) g := by
  intro n
  induction n with
  | zero =>
    intro N a _
    cases N with
    | empty =>
      cases a with
      | scalar =>
        refine ⟨.empty, ?_⟩
        simpa only [SymplecticNormalForm.toWord, List.nil_append, scalar, List.replicate_one]
          using adjacentSymplecticDerives_scalar (n := 0) g 1
      | H i => exact Fin.elim0 i
      | S i => exact Fin.elim0 i
      | CZ i _ _ => exact Fin.elim0 i
  | succ n ih =>
    intro N a ha
    obtain ⟨a, rfl⟩ := ha
    cases N with
    | step Z X M =>
      obtain ⟨r, Z', hZ'⟩ := hZ n Z a
      obtain ⟨s, X', hX'⟩ := X.adjacentSymplecticDerives_pushWord g r
      obtain ⟨M', hM'⟩ := adjacentSymplecticNormalizes_of_gateClosure g ih
        (M.toWord ++ s.toWord)
        ((isAdjacentWord_append _ _).mpr ⟨M.toWord_isAdjacent, s.isAdjacent_toWord⟩)
      refine ⟨.step Z' X' M', ?_⟩
      have h₁ := hZ'.append_left
        (relabel (initialEmbedding n) M.toWord ++ X.toWord)
      have h₂ := (hX'.append_right Z'.toWord).append_left
        (relabel (initialEmbedding n) M.toWord)
      have h₃ := (adjacentSymplecticDerives_initial g hM').append_right (X'.toWord ++ Z'.toWord)
      simp only [relabel_append, List.append_assoc] at h₁ h₂ h₃
      simpa only [SymplecticNormalForm.toWord, List.append_assoc] using
        h₁.trans (h₂.trans h₃)

/-- Once the concrete Z-sweep gate theorem is supplied, every adjacent word
has a restricted derivation to the recursive normal grammar. -/
theorem adjacentSymplecticNormalizes_of_zSweep (hZ : AdjacentZNormalGateClosure g) (n : ℕ) :
    AdjacentSymplecticNormalizes (n := n) g :=
  adjacentSymplecticNormalizes_of_gateClosure g (adjacentNormalFormGateClosure_of_zSweep g hZ n)

/-- The same Z-sweep interface suffices for exact Figure 1 completeness through
the already proved faithful signed-Pauli lifting theorem. -/
theorem adjacentFigure1Complete_of_zSweep (hZ : AdjacentZNormalGateClosure g) (n : ℕ) :
    AdjacentFigure1Complete (n := n) g :=
  adjacentFigure1Complete_of_normalFormGateClosure g
    (adjacentNormalFormGateClosure_of_zSweep g hZ n)

end QuditClifford.Circuit
