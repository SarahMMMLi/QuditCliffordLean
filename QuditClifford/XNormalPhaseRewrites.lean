import QuditClifford.SymplecticTwoWireD
import QuditClifford.RelabelRewrites

/-!
# Exact phase absorption through an arbitrary X-normal sweep

A phase power on the first wire passes through each D box and is absorbed
by the terminal E box. The proof follows the actual recursive word grammar.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]

/-- Change only the terminal E label by the phase absorbed at the first input. -/
def XNormal.absorbPhase (t : ZMod d) : {n : ℕ} → XNormal (ZMod d) n → XNormal (ZMod d) n
  | _, .finish c => .finish (c-t)
  | _, .step a b N => .step a b (N.absorbPhase t)

/-- A phase power crosses the first wire of any D box exactly. -/
theorem derives_D_Sexp_left {n : ℕ} (g : (ZMod d)ˣ) (a b t : ZMod d)
    (i j : Fin n) (hij : i ≠ j) :
    Derives g (dWord a b i j hij ++ Sexp i t) (Sexp j t ++ dWord a b i j hij) := by
  have h := (classWord_eq_iff_derives g _ _).mpr (derives_D_S_left g a b i j hij)
  have hs : SemiconjBy (classWord g (dWord a b i j hij))
      (classWord g [.S i]) (classWord g [.S j]) := h
  apply (classWord_eq_iff_derives g _ _).mp
  simpa only [classWord_append, Sexp, classWord_replicate] using hs.pow_right t.val

/-- A complete X-normal sweep absorbs any first-wire phase power by genuine
Figure 1 derivations, with no Pauli erasure or semantic normalization premise. -/
theorem XNormal.derives_absorbPhase (g : (ZMod d)ˣ) {n : ℕ}
    (N : XNormal (ZMod d) (n+1)) (t : ZMod d) :
    Derives g (N.toWord ++ Sexp 0 t) (N.absorbPhase t).toWord := by
  induction n with
  | zero =>
    cases N with
    | finish c =>
      have he : -c+t=-(c-t) := by ring
      simpa only [XNormal.toWord, XNormal.absorbPhase, eWord, he] using
        derives_Sexp_add g (0 : Fin 1) (-c) t
  | succ n ih =>
    cases N with
    | step a b N =>
      have hd := (derives_D_Sexp_left g a b t (0 : Fin (n+2)) 1 (by intro h; have hv := congrArg Fin.val h; norm_num at hv)).append_left
        (relabel (shiftEmbedding _) N.toWord)
      have hr := (derives_relabel g (shiftEmbedding _) (ih N)).append_right
        (dWord a b (0 : Fin (n+2)) 1 (by intro h; have hv := congrArg Fin.val h; norm_num at hv))
      simp only [XNormal.toWord, XNormal.absorbPhase, List.append_assoc]
      apply hd.trans
      simpa only [XNormal.toWord, XNormal.absorbPhase, relabel_append, relabel_Sexp,
        shiftEmbedding, Function.Embedding.coeFn_mk, List.append_assoc] using hr

/-- A single S is the residue-one instance of phase absorption. -/
theorem XNormal.derives_absorbS (g : (ZMod d)ˣ) {n : ℕ}
    (N : XNormal (ZMod d) (n+1)) :
    Derives g (N.toWord ++ [.S 0]) (N.absorbPhase 1).toWord := by
  simpa only [Sexp, ZMod.val_one, List.replicate_one] using N.derives_absorbPhase g 1

end QuditClifford.NormalBoxes
