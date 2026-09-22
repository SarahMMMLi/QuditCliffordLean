import QuditClifford.NormalIdentity
import QuditClifford.PauliLifting

/-!
# Syntactic normalization induction in the named-wire helper relation

This module connects closure of the literal recursive box grammar under a
primitive gate to exact completeness of the helper relation. For the paper’s
adjacent presentation, the corresponding restricted derivations are still
needed; this theorem does not assert them. The closure obligation is an
explicit hypothesis, not an axiom or a consequence of matrix uniqueness.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [Fact d.Prime] [NeZero d]

/-- The concrete exponent action determines every recursive box label. -/
theorem SymplecticNormalForm.eq_of_toWord_symplecticAction_eq
    (N M : SymplecticNormalForm (ZMod d) n)
    (h : ∀ p, symplecticAction d N.toWord p = symplecticAction d M.toWord p) : N = M := by
  apply SymplecticNormalForm.equiv_injective
  apply WireSymplectic.ext
  intro v
  have he := congrArg (wiresCoordinates d n).symm (h (wiresCoordinates d n v))
  change wireAction d N.toWord v = wireAction d M.toWord v at he
  simpa only [SymplecticNormalForm.toWord_action] using he

end QuditClifford.NormalBoxes

namespace QuditClifford.Circuit
open NormalBoxes
variable {d n : ℕ} [Fact d.Prime] [NeZero d]
variable (g : (ZMod d)ˣ)

/-- Every primitive word admits an actual erased derivation to the A/B/D/E grammar. -/
def SymplecticNormalizes : Prop :=
  ∀ w : Word n, ∃ N : SymplecticNormalForm (ZMod d) n,
    SymplecticDerives g w N.toWord

/-- The gate-pushing obligation in Lemma 4.2, stated on the literal normal grammar. -/
def NormalFormGateClosure : Prop :=
  ∀ (N : SymplecticNormalForm (ZMod d) n) (a : Gate n),
    ∃ M : SymplecticNormalForm (ZMod d) n,
      SymplecticDerives g (N.toWord ++ [a]) M.toWord

/-- The corrected identity seed and right-gate closure give an actual derivation
for every word by induction on its primitive letters. -/
theorem symplecticNormalizes_of_gateClosure
    (hstep : NormalFormGateClosure (n := n) g) : SymplecticNormalizes (n := n) g := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      exact ⟨identityNormal n, (derives_symplectic g (derives_identityNormal g n)).symm⟩
  | append_singleton w a ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨M, hM⟩ := hstep N a
      exact ⟨M, (hN.append_right [a]).trans hM⟩

/-- The local closure target is equivalent to syntactic normalization, with no
semantic completeness premise in either direction. -/
theorem symplecticNormalizes_iff_gateClosure :
    SymplecticNormalizes (n := n) g ↔ NormalFormGateClosure (n := n) g :=
  ⟨fun h N a => h (N.toWord ++ [a]), symplecticNormalizes_of_gateClosure g⟩

variable [Fact (Odd d)]

/-- When normalization derivations are available, their concrete box labels
are unique by soundness and the independently proved exponent classification. -/
theorem existsUnique_symplecticNormal_of_normalizes
    (hn : SymplecticNormalizes (n := n) g) (w : Word n) :
    ∃! N : SymplecticNormalForm (ZMod d) n, SymplecticDerives g w N.toWord := by
  obtain ⟨N, hN⟩ := hn w
  refine ⟨N, hN, ?_⟩
  intro M hM
  exact M.eq_of_toWord_symplecticAction_eq N
    (symplecticDerives_sound Fact.out g (hM.symm.trans hN))

/-- Syntactic normalization and semantic uniqueness establish erased completeness. -/
theorem symplecticErasureComplete_of_normalizes
    (hn : SymplecticNormalizes (n := n) g) : SymplecticErasureComplete (n := n) g := by
  intro u v huv
  obtain ⟨N, hN⟩ := hn u
  obtain ⟨M, hM⟩ := hn v
  have hNM : N = M := N.eq_of_toWord_symplecticAction_eq M (fun p =>
    (symplecticDerives_sound Fact.out g hN p).symm.trans
      ((huv p).trans (symplecticDerives_sound Fact.out g hM p)))
  exact hN.trans (hNM ▸ hM.symm)

/-- Conversely, erased completeness derives normalization to the independently
constructed semantic normal form. This implication assumes completeness. -/
theorem symplecticNormalizes_of_erasureComplete
    (hc : SymplecticErasureComplete (n := n) g) : SymplecticNormalizes (n := n) g := by
  intro w
  let F := generatedSymplecticHom (show Odd d from Fact.out) (generatedWord w)
  obtain ⟨N, hN, _⟩ := SymplecticNormalForm.existsUnique_equiv (fromPhaseSymplectic F)
  refine ⟨N, hc w N.toWord ?_⟩
  intro p
  rw [N.toWord_symplecticAction, hN]
  have hF := wireSymplecticEquiv.right_inv F
  calc
    symplecticAction d w p = F.val p :=
      (generatedSymplecticHom_word Fact.out w p).symm
    _ = (toPhaseSymplectic (fromPhaseSymplectic F)).val p :=
      (congrArg (fun T : symplecticGroup d n => T.val p) hF).symm

/-- All remaining work can be stated as actual gate closure of the concrete
normal syntax; semantic uniqueness alone never supplies this hypothesis. -/
theorem symplecticErasureComplete_iff_gateClosure :
    SymplecticErasureComplete (n := n) g ↔ NormalFormGateClosure (n := n) g := by
  constructor
  · intro hc
    exact (symplecticNormalizes_iff_gateClosure g).mp
      (symplecticNormalizes_of_erasureComplete g hc)
  · intro hs
    exact symplecticErasureComplete_of_normalizes g (symplecticNormalizes_of_gateClosure g hs)

variable [Fact (orderOf g = d-1)]

/-- Once multiwire box pushing establishes gate closure, the existing unique
Pauli correction restores exact equality with the selected scalar minus omega. -/
theorem figure1Complete_of_normalFormGateClosure
    (hstep : NormalFormGateClosure (n := n) g) : Figure1Complete (n := n) g :=
  figure1Complete_of_symplecticErasureComplete g
    ((symplecticErasureComplete_iff_gateClosure g).mpr hstep)

end QuditClifford.Circuit
