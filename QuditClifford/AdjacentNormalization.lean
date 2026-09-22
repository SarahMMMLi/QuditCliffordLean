import QuditClifford.AdjacentPresentation
import QuditClifford.AdjacentExactNormal

/-!
# Exact normalization and completeness in the source presentation

The already classified exact normal form is an adjacent word. Therefore
source-restricted completeness is equivalent to deriving normalization inside
the source-restricted relation itself. The unrestricted named-wire relation
is not used to supply derivations. `AdjacentCompleteness.lean` discharges this
normalization property by the actual restricted Z/X sweeps.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]

/-- Every source circuit reduces to its exact normal word through source circuits. -/
def AdjacentDerivablyNormalizes (hd : Odd d) (g : (ZMod d)ˣ) : Prop :=
  ∀ w : Word n, IsAdjacentWord w → AdjacentDerives g w (normalizeWord hd w)

/-- Semantic uniqueness and adjacency of the normal word leave precisely
the source-restricted syntactic reduction as the completeness obligation. -/
theorem adjacentFigure1Complete_iff_derivablyNormalizes (hd : Odd d) (g : (ZMod d)ˣ) :
    AdjacentFigure1Complete (n := n) g ↔ AdjacentDerivablyNormalizes (n := n) hd g := by
  constructor
  · intro hc w hw
    exact hc w (normalizeWord hd w) hw (normalizeWord_isAdjacent hd w)
      (denote_normalizeWord hd w).symm
  · intro hn u v hu hv huv
    exact (hn u hu).trans ((normalizeWord_eq_of_denote_eq hd huv) ▸ (hn v hv).symm)

/-- Arity zero already has normalization by source-restricted derivations. -/
theorem adjacentDerivablyNormalizes_zero (hd : Odd d) (g : (ZMod d)ˣ) :
    AdjacentDerivablyNormalizes (n := 0) hd g :=
  (adjacentFigure1Complete_iff_derivablyNormalizes hd g).mp
    (adjacentFigure1Complete_zero hd g)

/-- The complete one-qudit proof also yields its exact normal word in the
source-restricted presentation, including the signed Pauli correction. -/
theorem adjacentDerivablyNormalizes_one (g : (ZMod d)ˣ) [Fact (Odd d)]
    [Fact (orderOf g = d-1)] :
    AdjacentDerivablyNormalizes (n := 1) (Fact.out : Odd d) g :=
  (adjacentFigure1Complete_iff_derivablyNormalizes Fact.out g).mp
    (adjacentFigure1Complete_one g)

/-- The paper's exact equality criterion, once the stated normalization
derivations are established. This is conditional at arbitrary arity. -/
theorem adjacentDerives_iff_denote_eq_of_normalizes (hd : Odd d) (g : (ZMod d)ˣ)
    (hn : AdjacentDerivablyNormalizes (n := n) hd g)
    (u v : Word n) (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    AdjacentDerives g u v ↔ denote d u = denote d v :=
  ⟨adjacentDerives_sound hd g,
    (adjacentFigure1Complete_iff_derivablyNormalizes hd g).mpr hn u v hu hv⟩

end QuditClifford.Circuit
