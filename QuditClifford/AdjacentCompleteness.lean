import QuditClifford.AdjacentZNormalSweep
import QuditClifford.AdjacentNormalFormSweeps
import QuditClifford.AdjacentNormalization

/-!
# Exact completeness of Figure 1 on the source's adjacent alphabet

The literal Z/X box sweeps supply syntactic normalization at arbitrary arity.
Normal-label uniqueness gives completeness after explicit Pauli erasure;
faithful signed-Pauli lifting then recovers exact equality with scalar -omega.
No normalization, completeness, or presentation-comparison premise remains.

This is the selected-convention Theorem 4.10. It is distinct from the separate
literal eighteen-rule Figure 9 theorem, now proved in `Figure9Completeness`,
and from the refuted unrestricted
named-wire presentation.
-/
noncomputable section
namespace QuditClifford.Circuit
open NormalBoxes
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The concrete Z-normal gate closure is proved for every number of wires. -/
theorem adjacentZNormalGateClosure : AdjacentZNormalGateClosure g :=
  fun _ N a => N.adjacentSymplecticDerives_pushGate g a

/-- Every adjacent primitive preserves the recursive normal grammar by rewrites. -/
theorem adjacentNormalFormGateClosure (n : ℕ) : AdjacentNormalFormGateClosure (n := n) g :=
  adjacentNormalFormGateClosure_of_zSweep g (adjacentZNormalGateClosure g) n

/-- Every adjacent circuit has an actual restricted derivation to a normal word. -/
theorem adjacentSymplecticNormalizes (n : ℕ) : AdjacentSymplecticNormalizes (n := n) g :=
  adjacentSymplecticNormalizes_of_zSweep g (adjacentZNormalGateClosure g) n

/-- Equal exponent actions are completely characterized by the explicitly
Pauli-erased adjacent rewrite relation. -/
theorem adjacentSymplecticErasureComplete (n : ℕ) :
    AdjacentSymplecticErasureComplete (n := n) g :=
  adjacentSymplecticErasureComplete_of_normalizes g (adjacentSymplecticNormalizes g n)

/-- Exact Figure 1 completeness at arbitrary arity, with scalar minus omega. -/
theorem adjacentFigure1Complete (n : ℕ) : AdjacentFigure1Complete (n := n) g :=
  adjacentFigure1Complete_of_zSweep g (adjacentZNormalGateClosure g) n

/-- Exact semantic equality is equivalent to source-restricted syntactic rewriting. -/
theorem adjacentDerives_iff_denote_eq {n : ℕ} (u v : Word n)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    AdjacentDerives g u v ↔ denote d u = denote d v :=
  ⟨adjacentDerives_sound Fact.out g, adjacentFigure1Complete g n u v hu hv⟩

/-- The previously isolated concrete exact-normalization obligation is discharged. -/
theorem adjacentDerivablyNormalizes (n : ℕ) : AdjacentDerivablyNormalizes (n := n) Fact.out g :=
  (adjacentFigure1Complete_iff_derivablyNormalizes Fact.out g).mp (adjacentFigure1Complete g n)

/-- Every adjacent word has exactly one derivable recursive symplectic normal form. -/
theorem existsUnique_adjacentSymplecticNormal {n : ℕ} (w : Word n) (hw : IsAdjacentWord w) :
    ∃! N : SymplecticNormalForm (ZMod d) n, AdjacentSymplecticDerives g w N.toWord :=
  existsUnique_adjacentSymplecticNormal_of_normalizes g (adjacentSymplecticNormalizes g n) w hw

end QuditClifford.Circuit

namespace QuditClifford.Circuit
/-- Theorem 4.10 for the selected exact scalar convention and the paper's
adjacent tensor alphabet: sound and complete at every arity in each odd prime dimension. -/
theorem mainTheorem (d : ℕ) [NeZero d] : MainTheorem d := by
  intro hp hd g hg n
  letI : Fact d.Prime := ⟨hp⟩
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  exact ⟨figure1_sound hd g, adjacentFigure1Complete g n⟩
end QuditClifford.Circuit
