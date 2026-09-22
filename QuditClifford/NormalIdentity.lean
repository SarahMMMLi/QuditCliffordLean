import QuditClifford.RelabelRewrites
import QuditClifford.NormalCircuit

/-!
# A syntactically derived identity normal form

The seed uses the literal Figure 6 boxes: A(0,1), E(0), and paired B(0,0),
D(0,0). In particular E(0) repairs the incompatible E(d-1) printed in
equation (12). The cancellation below is exact and uses C3 at zero and C7.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [Fact d.Prime]

/-- The Z sweep bringing the last wire to the first with zero-labelled B boxes. -/
def identityZ : (n : ℕ) → ZNormal (ZMod d) (n+1)
  | 0 => .start ⟨0, 1, by simp⟩
  | n+1 => .step 0 0 (identityZ n)

/-- The inverse sweep, with E(0) on its terminal wire. -/
def identityX : (n : ℕ) → XNormal (ZMod d) (n+1)
  | 0 => .finish 0
  | n+1 => .step 0 0 (identityX n)

/-- Concrete labels for the normal form of the identity in every arity. -/
def identityNormal : (n : ℕ) → SymplecticNormalForm (ZMod d) n
  | 0 => .empty
  | n+1 => .step (identityZ n) (identityX n) (identityNormal n)

variable [NeZero d] (g : (ZMod d)ˣ)

/-- The Figure 6-compatible one-wire identity is an exact derivation. -/
theorem derives_identity_A_E (i : Fin (n+1)) :
    Derives g (eWord (0 : ZMod d) i ++ (⟨0, 1, by simp⟩ : ABox (ZMod d)).toWord i) [] := by
  simpa only [eWord, Sexp, neg_zero, ZMod.val_zero, List.replicate_zero,
    List.nil_append, ABox.toWord, dif_pos rfl, Units.mk0_one] using derives_multiplier_one g i

/-- The inverse B/D sweeps cancel using genuine contextual rewrites. -/
theorem derives_identity_sweeps : (n : ℕ) →
    Derives g ((identityX (d := d) n).toWord ++ (identityZ (d := d) n).toWord) []
  | 0 => derives_identity_A_E g 0
  | n+1 => by
    have hij : (0 : Fin (n+2)) ≠ 1 := by
      intro h
      have hh := congrArg Fin.val h
      simp at hh
    have ih := derives_relabel g (shiftEmbedding (n+1)) (derives_identity_sweeps n)
    have hs : Derives g
        (dWord (0 : ZMod d) 0 0 1 hij ++ bWord (0 : ZMod d) 0 0 1 hij : Word (n+2)) [] := by
      simpa [dWord, bWord, power] using
        (show Derives g (Circuit.SWAP (d := d) (0 : Fin (n+2)) 1 hij ++
          Circuit.SWAP (d := d) (0 : Fin (n+2)) 1 hij) [] from
            .rule (Or.inr (.C7 0 1 hij)))
    have ht := hs.context (relabel (shiftEmbedding (n+1)) (identityX (d := d) n).toWord)
      (relabel (shiftEmbedding (n+1)) (identityZ (d := d) n).toWord)
    simp only [List.append_nil, List.nil_append] at ht
    simp only [relabel_append, relabel_nil] at ih
    simpa only [identityX, identityZ, XNormal.toWord, ZNormal.toWord,
      List.append_assoc] using ht.trans ih

/-- The actual recursive normal word for identity reduces to the empty circuit. -/
theorem derives_identityNormal : (n : ℕ) →
    Derives g (identityNormal (d := d) n).toWord []
  | 0 => .refl _
  | n+1 => by
    have ht := derives_relabel g (initialEmbedding n) (derives_identityNormal n)
    have hs := derives_identity_sweeps g n
    simpa only [identityNormal, SymplecticNormalForm.toWord, relabel_nil,
      List.nil_append, List.append_assoc] using ht.append hs

end QuditClifford.NormalBoxes
