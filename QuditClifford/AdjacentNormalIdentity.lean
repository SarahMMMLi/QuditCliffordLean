import QuditClifford.AdjacentOneWireAlgebra
import QuditClifford.NormalIdentity

/-!
# Exact identity normal form in the adjacent presentation

The literal Figure 6 seed uses A(0,1) and E(0), together with cancelling
B(0,0)/D(0,0) sweeps. Every primitive rule instance below stays in the
canonical increasing adjacent alphabet. This is a concrete identity seed;
it assumes no general normalization or completeness theorem.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [Fact d.Prime] [NeZero d] (g : (ZMod d)ˣ)

/-- The Figure 6-compatible A/E identity seed in the restricted relation. -/
theorem adjacentDerives_identity_A_E (i : Fin (n+1)) :
    AdjacentDerives g
      (eWord (0 : ZMod d) i ++ (⟨0, 1, by simp⟩ : ABox (ZMod d)).toWord i) [] := by
  simpa only [eWord, Sexp, neg_zero, ZMod.val_zero, List.replicate_zero,
    List.nil_append, ABox.toWord, dif_pos rfl, Units.mk0_one]
    using adjacentDerives_multiplier_one g i

/-- Paired zero-labelled B/D sweeps cancel using adjacent contextual rewrites. -/
theorem adjacentDerives_identity_sweeps : (n : ℕ) →
    AdjacentDerives g ((identityX (d := d) n).toWord ++ (identityZ (d := d) n).toWord) []
  | 0 => adjacentDerives_identity_A_E g 0
  | n+1 => by
    have hij : (0 : Fin (n+2)) ≠ 1 := by
      intro h
      have hh := congrArg Fin.val h
      simp at hh
    have hadj : (Gate.CZ (0 : Fin (n+2)) 1 hij).IsAdjacent := by
      simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one] using
        Gate.isAdjacent_CZ (0 : Fin (n+1)) (adjacent_ne 0)
    have ih := adjacentDerives_shift g (adjacentDerives_identity_sweeps n)
    have hs : AdjacentDerives g
        (dWord (0 : ZMod d) 0 0 1 hij ++ bWord (0 : ZMod d) 0 0 1 hij : Word (n+2)) [] := by
      simpa [dWord, bWord, power] using adjacentDerives_SWAP_sq g 0 1 hij hadj
    have ht := hs.context (relabel (shiftEmbedding (n+1)) (identityX (d := d) n).toWord)
      (relabel (shiftEmbedding (n+1)) (identityZ (d := d) n).toWord)
    simp only [List.append_nil, List.nil_append] at ht
    simp only [relabel_append, relabel_nil] at ih
    simpa only [identityX, identityZ, XNormal.toWord, ZNormal.toWord,
      List.append_assoc] using ht.trans ih

/-- The recursive identity normal word reduces exactly to the empty circuit. -/
theorem adjacentDerives_identityNormal : (n : ℕ) →
    AdjacentDerives g (identityNormal (d := d) n).toWord []
  | 0 => .refl _
  | n+1 => by
    have ht := adjacentDerives_initial g (adjacentDerives_identityNormal n)
    have hs := adjacentDerives_identity_sweeps g n
    simpa only [identityNormal, SymplecticNormalForm.toWord, relabel_nil,
      List.nil_append, List.append_assoc] using ht.append hs

end QuditClifford.NormalBoxes
