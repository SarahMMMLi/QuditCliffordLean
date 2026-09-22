import QuditClifford.AdjacentZNormalHead
import QuditClifford.AdjacentZNormalHeadCZ
import QuditClifford.AdjacentBDirtyPush

/-! # Recursive Z-normal gate pushing in the adjacent presentation -/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem start_pushTail {n : ℕ} (A : ABox (ZMod d)) (a : AdjacentGate n) :
    AdjacentSymplecticDerives g
      (A.toWord (0 : Fin (n+1)) ++ [a.toGate.relabel (shiftEmbedding n)])
      (ZSweepWord.toWord [ZSweepGate.fromTail a] ++ A.toWord 0) := by
  have h := adjacentDerives_relabel_interchange g
    (singleWireEmbedding (0 : Fin (n+1))) (shiftEmbedding n)
    (fun _ j => (Fin.succ_ne_zero j).symm)
    (A.toWord (0 : Fin 1)) [a.toGate]
    (isAdjacentWord_singleWire 0 _) (by simpa only [relabel_cons, relabel_nil] using
      (AdjacentWord.isAdjacent_toWord [a]).shift)
  simpa only [ABox.relabel_toWord, singleWireEmbedding, Function.Embedding.coeFn_mk,
    relabel_cons, relabel_nil, ZSweepWord.toWord_cons, ZSweepWord.toWord_nil,
    ZSweepGate.toGate_fromTail] using adjacentDerives_symplectic g h

private theorem step_pushTail {n : ℕ} (a b : ZMod d) (N : ZNormal (ZMod d) (n+1))
    (q : AdjacentGate (n+1))
    (hN : ∃ (r : ZSweepWord n) (N' : ZNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [q.toGate]) (r.toWord ++ N'.toWord)) :
    ∃ (r : ZSweepWord (n+1)) (N' : ZNormal (ZMod d) (n+2)),
      AdjacentSymplecticDerives g
        ((ZNormal.step a b N).toWord ++ [q.toGate.relabel (shiftEmbedding (n+1))])
        (r.toWord ++ N'.toWord) := by
  obtain ⟨w, N', hN⟩ := hN
  obtain ⟨r, hr⟩ := adjacentSymplecticDerives_B_dirtyWord g a b w
  refine ⟨r, .step a b N', ?_⟩
  have h₁ := (adjacentSymplecticDerives_shift g hN).append_left
    (bWord a b (0 : Fin (n+2)) 1 (adjacent_ne (0 : Fin (n+1))))
  have h₂ := hr.append_right (relabel (shiftEmbedding (n+1)) N'.toWord)
  simp only [relabel_append, relabel_cons, relabel_nil, List.append_assoc] at h₁ h₂
  simpa only [ZNormal.toWord, List.append_assoc] using h₁.trans h₂

variable (headCZ : ∀ {n : ℕ} (N : ZNormal (ZMod d) (n+2)),
  ∃ (r : ZSweepWord (n+1)) (N' : ZNormal (ZMod d) (n+2)),
    AdjacentSymplecticDerives g (N.toWord ++ [.CZ 0 1 (adjacent_ne (0 : Fin (n+1)))])
      (r.toWord ++ N'.toWord))

include headCZ in
/-- The arity recursion reduces Z gate closure to the proved head cases and
the head controlled-phase branch. Tail dirty words pass B with fixed labels. -/
theorem ZNormal.adjacentSymplecticDerives_pushGate_of_headCZ {n : ℕ}
    (N : ZNormal (ZMod d) (n+1)) (q : AdjacentGate (n+1)) :
    ∃ (r : ZSweepWord n) (N' : ZNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [q.toGate]) (r.toWord ++ N'.toWord) := by
  induction n with
  | zero =>
    cases q with
    | scalar =>
      refine ⟨[], N, ?_⟩
      have h : AdjacentSymplecticDerives g [.scalar] ([] : Word 1) :=
        .rule ⟨Or.inl (Or.inr ⟨rfl, rfl⟩), by simp, by simp⟩
      simpa only [AdjacentGate.toGate, ZSweepWord.toWord_nil, List.nil_append, List.append_nil]
        using h.append_left N.toWord
    | H i =>
      have hi : i=0 := Fin.ext (by omega)
      subst i
      exact N.adjacentSymplecticDerives_pushHeadH g
    | S i =>
      have hi : i=0 := Fin.ext (by omega)
      subst i
      exact N.adjacentSymplecticDerives_pushHeadS g
    | CZ i => exact Fin.elim0 i
  | succ n ih =>
    cases q with
    | scalar =>
      refine ⟨[], N, ?_⟩
      have h : AdjacentSymplecticDerives g [.scalar] ([] : Word (n+2)) :=
        .rule ⟨Or.inl (Or.inr ⟨rfl, rfl⟩), by simp, by simp⟩
      simpa only [AdjacentGate.toGate, ZSweepWord.toWord_nil, List.nil_append, List.append_nil]
        using h.append_left N.toWord
    | H i =>
      refine Fin.cases (N.adjacentSymplecticDerives_pushHeadH g) (fun j => ?_) i
      cases N with
      | start A => exact ⟨[ZSweepGate.fromTail (.H j)], .start A, start_pushTail g A (.H j)⟩
      | step a b N => exact step_pushTail g a b N (.H j) (ih N (.H j))
    | S i =>
      refine Fin.cases (N.adjacentSymplecticDerives_pushHeadS g) (fun j => ?_) i
      cases N with
      | start A => exact ⟨[ZSweepGate.fromTail (.S j)], .start A, start_pushTail g A (.S j)⟩
      | step a b N => exact step_pushTail g a b N (.S j) (ih N (.S j))
    | CZ i =>
      refine Fin.cases (headCZ N) (fun j => ?_) i
      cases N with
      | start A => exact ⟨[ZSweepGate.fromTail (.CZ j)], .start A, start_pushTail g A (.CZ j)⟩
      | step a b N => exact step_pushTail g a b N (.CZ j) (ih N (.CZ j))

/-- Every adjacent primitive pushes through any Z-normal sweep by actual
source-restricted rewrites, leaving a typed dirty residual. -/
theorem ZNormal.adjacentSymplecticDerives_pushGate {n : ℕ}
    (N : ZNormal (ZMod d) (n+1)) (q : AdjacentGate (n+1)) :
    ∃ (r : ZSweepWord n) (N' : ZNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [q.toGate]) (r.toWord ++ N'.toWord) :=
  N.adjacentSymplecticDerives_pushGate_of_headCZ g
    (fun M => M.adjacentSymplecticDerives_pushHeadCZ g) q

end QuditClifford.NormalBoxes
