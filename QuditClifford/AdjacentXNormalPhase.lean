import QuditClifford.AdjacentBoxCases
import QuditClifford.AdjacentPairEmbedding
import QuditClifford.XNormalPhaseRewrites

/-!
# Exact phase absorption through X-normal sweeps in the adjacent presentation

The proof follows the recursive X-normal grammar. Its local step replays the
checked two-wire D/S relation at a neighboring pair and extends it to a finite
phase power by contextual rewrites. The terminal E box absorbs the phase by
C1 exponent addition. All intermediate rules remain in the adjacent alphabet.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- A phase power crosses the first wire of any neighboring D box exactly. -/
theorem adjacentDerives_D_Sexp_left {n : ℕ} (a b t : ZMod d) (i : Fin (n+1)) :
    AdjacentDerives g
      (dWord a b i.castSucc i.succ (adjacent_ne i) ++ Sexp i.castSucc t)
      (Sexp i.succ t ++ dWord a b i.castSucc i.succ (adjacent_ne i)) := by
  have h : AdjacentDerives g
      (dWord a b i.castSucc i.succ (adjacent_ne i) ++ [.S i.castSucc])
      ([.S i.succ] ++ dWord a b i.castSucc i.succ (adjacent_ne i)) := by
    simpa only [relabel_append, relabel_dWord, relabel_cons, relabel_nil,
      Gate.relabel, adjacentPairEmbedding_zero, adjacentPairEmbedding_one] using
      adjacentDerives_pair g i (adjacentDerives_D_S_left g a b)
  exact AdjacentDerives.transport_replicate g h t.val

/-- An arbitrary X-normal sweep absorbs a first-wire phase power through an
actual recursive derivation in the restricted exact presentation. -/
theorem XNormal.adjacentDerives_absorbPhase {n : ℕ}
    (N : XNormal (ZMod d) (n+1)) (t : ZMod d) :
    AdjacentDerives g (N.toWord ++ Sexp 0 t) (N.absorbPhase t).toWord := by
  induction n with
  | zero =>
    cases N with
    | finish c =>
      have he : -c+t=-(c-t) := by ring
      simpa only [XNormal.toWord, XNormal.absorbPhase, eWord, he] using
        adjacentDerives_Sexp_add g (0 : Fin 1) (-c) t
  | succ n ih =>
    cases N with
    | step a b N =>
      have hd := (adjacentDerives_D_Sexp_left g a b t (0 : Fin (n+1))).append_left
        (relabel (shiftEmbedding _) N.toWord)
      have hr := (adjacentDerives_shift g (ih N)).append_right
        (dWord a b (0 : Fin (n+2)) 1
          (by intro h; have hv := congrArg Fin.val h; norm_num at hv))
      simp only [XNormal.toWord, XNormal.absorbPhase, List.append_assoc]
      apply hd.trans
      simpa only [XNormal.toWord, XNormal.absorbPhase, relabel_append, relabel_Sexp,
        shiftEmbedding, Function.Embedding.coeFn_mk, List.append_assoc] using hr

/-- A single S is the residue-one specialization of exact phase absorption. -/
theorem XNormal.adjacentDerives_absorbS {n : ℕ}
    (N : XNormal (ZMod d) (n+1)) :
    AdjacentDerives g (N.toWord ++ [.S 0]) (N.absorbPhase 1).toWord := by
  simpa only [Sexp, ZMod.val_one, List.replicate_one] using N.adjacentDerives_absorbPhase g 1

end QuditClifford.NormalBoxes
