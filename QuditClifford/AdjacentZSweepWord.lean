import QuditClifford.NormalSweepSyntax
import QuditClifford.AdjacentPairEmbedding
import QuditClifford.AdjacentTripleEmbedding
import QuditClifford.AdjacentOneWireRewrites
import QuditClifford.AdjacentThreeWireTransport

/-! # Recognizing and embedding the literal dirty Z-sweep grammar -/
namespace QuditClifford.NormalBoxes
open Circuit
variable {d m n : ℕ}

/-- A primitive word is a dirty Z-sweep word exactly when it is adjacent and
has no Fourier gate on the distinguished head wire. -/
def IsZSweepWord (w : Word (n+1)) : Prop :=
  IsAdjacentWord w ∧ ∀ i, Gate.H i ∈ w → i ≠ 0

/-- The concrete predicate has the same words as the typed dirty grammar. -/
theorem isZSweepWord_iff_exists (w : Word (n+1)) :
    IsZSweepWord w ↔ ∃ v : ZSweepWord n, v.toWord=w := by
  constructor
  · intro hw
    induction w with
    | nil => exact ⟨[], rfl⟩
    | cons a w ih =>
      obtain ⟨b, rfl⟩ := hw.1 a (by simp)
      obtain ⟨v, hv⟩ := ih ⟨fun c hc => hw.1 c (by simp [hc]),
        fun i hi => hw.2 i (by simp [hi])⟩
      have hb : ∃ c : ZSweepGate n, c.toGate=b.toGate := by
        cases b with
        | scalar => exact ⟨.scalar, rfl⟩
        | S i => exact ⟨.S i, rfl⟩
        | H i =>
          have hi : i ≠ 0 := hw.2 i (by simp [AdjacentGate.toGate])
          cases i using Fin.cases with
          | zero => exact (hi rfl).elim
          | succ i => exact ⟨.H i, rfl⟩
        | CZ i => exact ⟨.CZ i, rfl⟩
      obtain ⟨c, hc⟩ := hb
      exact ⟨c::v, by rw [ZSweepWord.toWord_cons, hv, hc]⟩
  · rintro ⟨v, rfl⟩
    refine ⟨v.isAdjacent_toWord, ?_⟩
    intro i hi
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hi
    cases a with
    | scalar => cases ha
    | S j => cases ha
    | CZ j => cases ha
    | H j =>
      have he : j.succ=i := Gate.H.inj ha
      rw [← he]
      exact Fin.succ_ne_zero j

@[simp] theorem isZSweepWord_nil : IsZSweepWord ([] : Word (n+1)) := by simp [IsZSweepWord]
@[simp] theorem isZSweepWord_append (u v : Word (n+1)) :
    IsZSweepWord (u++v) ↔ IsZSweepWord u ∧ IsZSweepWord v := by
  simp only [IsZSweepWord, isAdjacentWord_append, List.mem_append]
  aesop
@[simp] theorem isZSweepWord_scalar_gate : IsZSweepWord ([.scalar] : Word (n+1)) := by
  simp [IsZSweepWord]
@[simp] theorem isZSweepWord_S (i : Fin (n+1)) : IsZSweepWord [.S i] := by
  simp [IsZSweepWord]
@[simp] theorem isZSweepWord_H (i : Fin (n+1)) : IsZSweepWord [.H i] ↔ i ≠ 0 := by
  simp [IsZSweepWord]
@[simp] theorem isZSweepWord_CZ (i : Fin n) :
    IsZSweepWord [.CZ i.castSucc i.succ (adjacent_ne i)] := by
  simp [IsZSweepWord, Gate.isAdjacent_CZ]

theorem IsZSweepWord.replicate (a : Gate (n+1))
    (ha : IsZSweepWord [a]) (k : ℕ) : IsZSweepWord (List.replicate k a) := by
  induction k with
  | zero => exact isZSweepWord_nil
  | succ k ih =>
    simpa only [List.replicate_succ, List.singleton_append] using
      (isZSweepWord_append [a] (List.replicate k a)).mpr ⟨ha, ih⟩

theorem IsZSweepWord.power {w : Word (n+1)} (hw : IsZSweepWord w) (k : ℕ) :
    IsZSweepWord (power w k) := by
  induction k with
  | zero => exact isZSweepWord_nil
  | succ k ih => exact (isZSweepWord_append _ _).mpr ⟨hw, ih⟩

@[simp] theorem isZSweepWord_scalar (k : ℕ) : IsZSweepWord (scalar (n := n+1) k) :=
  IsZSweepWord.replicate _ isZSweepWord_scalar_gate k
@[simp] theorem isZSweepWord_Sexp (i : Fin (n+1)) (a : ZMod d) : IsZSweepWord (Sexp i a) :=
  IsZSweepWord.replicate _ (isZSweepWord_S i) a.val

theorem IsZSweepWord.inverseWord {w : Word (n+1)} (hw : IsZSweepWord w) :
    IsZSweepWord (inverseWord d w) := by
  obtain ⟨v, rfl⟩ := (isZSweepWord_iff_exists w).mp hw
  apply (isZSweepWord_iff_exists _).mpr
  exact ⟨v.inverseWord d, v.toWord_inverseWord d⟩

/-- A placement fixing the head and preserving adjacency also preserves dirty words. -/
theorem IsZSweepWord.relabel {w : Word (m+1)} (hw : IsZSweepWord w)
    (ι : Fin (m+1) ↪ Fin (n+1)) (h0 : ι 0=0)
    (hι : ∀ a : Gate (m+1), a.IsAdjacent → (a.relabel ι).IsAdjacent) :
    IsZSweepWord (Circuit.relabel ι w) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hι b (hw.1 b hb)
  · intro i hi
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hi
    cases a with
    | scalar => cases he
    | S j => cases he
    | CZ j k hjk => cases he
    | H j =>
      have he' : ι j=i := Gate.H.inj he
      intro hz
      apply hw.2 j ha
      apply ι.injective
      exact he'.trans (hz.trans h0.symm)

theorem IsZSweepWord.relabel_pair {w : Word 2} (hw : IsZSweepWord w) :
    IsZSweepWord (Circuit.relabel (adjacentPairEmbedding (0 : Fin (n+1))) w) :=
  hw.relabel _ (by simp) (fun _ ha => Gate.isAdjacent_relabel_adjacentPair ha 0)

theorem IsZSweepWord.relabel_triple {w : Word 3} (hw : IsZSweepWord w) :
    IsZSweepWord (Circuit.relabel (adjacentTripleEmbedding (0 : Fin (n+1))) w) :=
  hw.relabel _ (by simp) (fun _ ha => Gate.isAdjacent_relabel_adjacentTriple ha 0)

variable [NeZero d]

theorem isZSweepWord_singleWire (i : Fin (n+1)) (hi : i ≠ 0) (w : Word 1) :
    IsZSweepWord (Circuit.relabel (singleWireEmbedding i) w) := by
  refine ⟨isAdjacentWord_singleWire i w, ?_⟩
  intro j hj
  obtain ⟨a, _, ha⟩ := List.mem_map.mp hj
  cases a with
  | scalar => cases ha
  | S k => cases ha
  | CZ k l hkl => cases ha
  | H k =>
    have he : i=j := Gate.H.inj ha
    exact he ▸ hi

theorem isZSweepWord_multiplier (i : Fin (n+1)) (a : (ZMod d)ˣ) (hi : i ≠ 0) :
    IsZSweepWord (Circuit.multiplier i a) := by
  simpa only [relabel_multiplier, singleWireEmbedding, Function.Embedding.coeFn_mk] using
    isZSweepWord_singleWire i hi (Circuit.multiplier (0 : Fin 1) a)

omit [NeZero d] in
/-- The routed remote phase uses SWAPs only on the two trailing wires. -/
theorem isZSweepWord_CIZ012 :
    IsZSweepWord (CIZ (d := d) (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)) := by
  refine ⟨AdjacentThreeWire.remote_adj, ?_⟩
  intro i hi
  simp only [Circuit.CIZ, Circuit.SWAP, Circuit.power, Circuit.scalar,
    List.mem_append, List.mem_cons, List.mem_replicate, List.mem_flatten, List.mem_map,
    List.not_mem_nil, or_false] at hi
  aesop

end QuditClifford.NormalBoxes
