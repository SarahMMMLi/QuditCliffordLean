import QuditClifford.AdjacentNormalIdentity
import QuditClifford.AdjacentPauliLifting

/-!
# Restricted normalization from closure of the literal normal grammar

The exact adjacent identity seed supplies the base case. Closure under an
adjacent primitive then gives guarded normalization by induction on words.
Gate closure remains an explicit hypothesis throughout: none of the results
below itself supplies the box-pushing induction. `AdjacentCompleteness.lean`
instantiates closure with the independently proved restricted Z/X sweeps.
-/
noncomputable section
namespace QuditClifford.Circuit
open NormalBoxes
variable {d n : ℕ} [Fact d.Prime] [NeZero d]
variable (g : (ZMod d)ˣ)

/-- Every adjacent word has a derivation to the literal recursive normal grammar. -/
def AdjacentSymplecticNormalizes : Prop :=
  ∀ w : Word n, IsAdjacentWord w → ∃ N : SymplecticNormalForm (ZMod d) n,
    AdjacentSymplecticDerives g w N.toWord

/-- The local gate-pushing property, in the restricted relation. -/
def AdjacentNormalFormGateClosure : Prop :=
  ∀ (N : SymplecticNormalForm (ZMod d) n) (a : Gate n), a.IsAdjacent →
    ∃ M : SymplecticNormalForm (ZMod d) n,
      AdjacentSymplecticDerives g (N.toWord ++ [a]) M.toWord

/-- The exact identity seed and restricted gate closure normalize every
adjacent word through actual guarded rewrites. -/
theorem adjacentSymplecticNormalizes_of_gateClosure
    (hstep : AdjacentNormalFormGateClosure (n := n) g) :
    AdjacentSymplecticNormalizes (n := n) g := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro _
      exact ⟨identityNormal n,
        (adjacentDerives_symplectic g (adjacentDerives_identityNormal g n)).symm⟩
  | append_singleton w a ih =>
      intro hw
      have hwa := (isAdjacentWord_append _ _).mp hw
      obtain ⟨N, hN⟩ := ih hwa.1
      obtain ⟨M, hM⟩ := hstep N a ((isAdjacentWord_cons _ _).mp hwa.2).1
      exact ⟨M, (hN.append_right [a]).trans hM⟩

/-- Restricted gate closure and restricted syntactic normalization are equivalent. -/
theorem adjacentSymplecticNormalizes_iff_gateClosure :
    AdjacentSymplecticNormalizes (n := n) g ↔ AdjacentNormalFormGateClosure (n := n) g :=
  ⟨fun h N a ha => h (N.toWord ++ [a])
      ((isAdjacentWord_append _ _).mpr ⟨N.toWord_isAdjacent, by simp [ha]⟩),
    adjacentSymplecticNormalizes_of_gateClosure g⟩

private theorem normal_eq_of_action_eq (N M : SymplecticNormalForm (ZMod d) n)
    (h : ∀ p, symplecticAction d N.toWord p = symplecticAction d M.toWord p) : N = M := by
  apply SymplecticNormalForm.equiv_injective
  apply WireSymplectic.ext
  intro v
  have he := congrArg (wiresCoordinates d n).symm (h (wiresCoordinates d n v))
  change wireAction d N.toWord v = wireAction d M.toWord v at he
  simpa only [SymplecticNormalForm.toWord_action] using he

variable [Fact (Odd d)]

/-- Soundness and the independently proved label classification make an
already derived restricted normal form unique. -/
theorem existsUnique_adjacentSymplecticNormal_of_normalizes
    (hn : AdjacentSymplecticNormalizes (n := n) g) (w : Word n) (hw : IsAdjacentWord w) :
    ∃! N : SymplecticNormalForm (ZMod d) n, AdjacentSymplecticDerives g w N.toWord := by
  obtain ⟨N, hN⟩ := hn w hw
  refine ⟨N, hN, ?_⟩
  intro M hM
  exact normal_eq_of_action_eq M N
    (adjacentSymplecticDerives_sound Fact.out g (hM.symm.trans hN))

/-- Actual restricted normalization derivations imply erased completeness. -/
theorem adjacentSymplecticErasureComplete_of_normalizes
    (hn : AdjacentSymplecticNormalizes (n := n) g) :
    AdjacentSymplecticErasureComplete (n := n) g := by
  intro u v hu hv huv
  obtain ⟨N, hN⟩ := hn u hu
  obtain ⟨M, hM⟩ := hn v hv
  have hNM : N = M := normal_eq_of_action_eq N M (fun p =>
    (adjacentSymplecticDerives_sound Fact.out g hN p).symm.trans
      ((huv p).trans (adjacentSymplecticDerives_sound Fact.out g hM p)))
  exact hN.trans (hNM ▸ hM.symm)

/-- Assuming restricted erased completeness, semantic classification supplies
the target labels and completeness supplies their derivation. -/
theorem adjacentSymplecticNormalizes_of_erasureComplete
    (hc : AdjacentSymplecticErasureComplete (n := n) g) :
    AdjacentSymplecticNormalizes (n := n) g := by
  intro w hw
  let F := generatedSymplecticHom (show Odd d from Fact.out) (generatedWord w)
  obtain ⟨N, hN, _⟩ := SymplecticNormalForm.existsUnique_equiv (fromPhaseSymplectic F)
  refine ⟨N, hc w N.toWord hw N.toWord_isAdjacent ?_⟩
  intro p
  rw [N.toWord_symplecticAction, hN]
  have hF := wireSymplecticEquiv.right_inv F
  calc
    symplecticAction d w p = F.val p :=
      (generatedSymplecticHom_word Fact.out w p).symm
    _ = (toPhaseSymplectic (fromPhaseSymplectic F)).val p :=
      (congrArg (fun T : symplecticGroup d n => T.val p) hF).symm

/-- The remaining erased completeness obligation can be stated precisely as
closure of the recursive grammar under canonical adjacent primitives. -/
theorem adjacentSymplecticErasureComplete_iff_gateClosure :
    AdjacentSymplecticErasureComplete (n := n) g ↔
      AdjacentNormalFormGateClosure (n := n) g := by
  constructor
  · intro hc
    exact (adjacentSymplecticNormalizes_iff_gateClosure g).mp
      (adjacentSymplecticNormalizes_of_erasureComplete g hc)
  · intro hs
    exact adjacentSymplecticErasureComplete_of_normalizes g
      (adjacentSymplecticNormalizes_of_gateClosure g hs)

variable [Fact (orderOf g = d-1)]

/-- Restricted gate closure completes the exact adjacent target by the proved
signed Pauli lifting theorem, retaining Figure 1's scalar minus omega. -/
theorem adjacentFigure1Complete_of_normalFormGateClosure
    (hstep : AdjacentNormalFormGateClosure (n := n) g) :
    AdjacentFigure1Complete (n := n) g :=
  adjacentFigure1Complete_of_symplecticErasureComplete g
    ((adjacentSymplecticErasureComplete_iff_gateClosure g).mpr hstep)

/-- No separate projective-to-exact obligation remains once adjacent gate
closure is established; the equivalence itself proves neither side outright. -/
theorem adjacentFigure1Complete_iff_normalFormGateClosure :
    AdjacentFigure1Complete (n := n) g ↔ AdjacentNormalFormGateClosure (n := n) g :=
  (adjacentFigure1Complete_iff_symplecticErasureComplete g).trans
    (adjacentSymplecticErasureComplete_iff_gateClosure g)

end QuditClifford.Circuit
