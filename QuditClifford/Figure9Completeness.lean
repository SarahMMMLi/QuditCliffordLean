import QuditClifford.Figure9Comparison
import QuditClifford.Figure9Soundness
import QuditClifford.Figure9BoxCases

/-!
# Theorem 4.4 for the corrected Figure 9 presentation

The actual eighteen source equations are sound and complete for symplectic
exponent actions. Their syntactic derivations are equivalent to the established
adjacent Figure 1 derivations with explicit scalar and Pauli erasure. The
separate exact theorem retains the scalar generator minus omega.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The literal Figure 9 presentation characterizes equality up to Pauli
corrections, for all numbers of wires. -/
theorem figure9Derives_iff_symplecticAction_eq (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) ↔
      ∀ p, symplecticAction d u p = symplecticAction d v p := by
  constructor
  · intro h p
    simpa only [symplecticAction_eraseScalar] using figure9Derives_sound g Fact.out h p
  · exact figure9Complete g hu hv

/-- Both presentations describe the same syntactic relation on their respective
alphabets; Pauli erasure is derived on the Figure 9 side. -/
theorem figure9Derives_iff_adjacentSymplecticDerives (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) ↔ AdjacentSymplecticDerives g u v := by
  constructor
  · intro h
    exact adjacentSymplecticErasureComplete g n u v hu hv
      ((figure9Derives_iff_symplecticAction_eq g u v hu hv).mp h)
  · exact adjacentSymplecticDerives_figure9 g

/-- Every source circuit has a unique literal normal form derivable using
only Figure 9's eighteen equations. -/
theorem existsUnique_figure9Normal (w : Word n) (hw : IsAdjacentWord w) :
    ∃! N : NormalBoxes.SymplecticNormalForm (ZMod d) n,
      Figure9Derives g (eraseScalar w) (eraseScalar N.toWord) := by
  obtain ⟨N,hN,huniq⟩ := existsUnique_adjacentSymplecticNormal g w hw
  refine ⟨N, adjacentSymplecticDerives_figure9 g hN, ?_⟩
  intro M hM
  exact huniq M ((figure9Derives_iff_adjacentSymplecticDerives g w M.toWord
    hw M.toWord_isAdjacent).mp hM)

end QuditClifford.Circuit
namespace QuditClifford.Circuit

/-- Theorem 4.4: exactly the corrected eighteen Figure 9 schemas give sound
and complete symplectic rewriting on the adjacent tensor alphabet. -/
theorem figure9MainTheorem (d : ℕ) [NeZero d] (hp : d.Prime) (hd : Odd d)
    (g : (ZMod d)ˣ) (hg : orderOf g = d-1) (n : ℕ)
    (u v : Word n) (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) ↔
      ∀ p, symplecticAction d u p = symplecticAction d v p := by
  letI : Fact d.Prime := ⟨hp⟩
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  exact figure9Derives_iff_symplecticAction_eq g u v hu hv

end QuditClifford.Circuit
