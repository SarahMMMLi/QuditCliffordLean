import QuditClifford.Figure9Syntax
import QuditClifford.AdjacentPairEmbedding

/-! # Transport of the eighteen equations through canonical wire embeddings -/
noncomputable section
namespace QuditClifford.Circuit
variable {d m n : ℕ}

@[simp] theorem relabel_XC (ι : Fin m ↪ Fin n) (i j : Fin m) (hij : i ≠ j) :
    relabel ι (XC i j hij) = XC (ι i) (ι j) (fun h => hij (ι.injective h)) := by
  simp [XC, Gate.relabel]

variable [NeZero d] (g : (ZMod d)ˣ)

/-- All eighteen schemas commute with injective renaming before locality is guarded. -/
theorem Figure9Rule.relabel (ι : Fin m ↪ Fin n) {u v : Word m}
    (h : Figure9Rule g u v) : Figure9Rule g (relabel ι u) (relabel ι v) := by
  cases h with
  | C1 i => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using (Figure9Rule.C1 (g := g) (ι i))
  | C2 i => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using (Figure9Rule.C2 (g := g) (ι i))
  | C3 i k => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using (Figure9Rule.C3 (g := g) (ι i) k)
  | C4 i => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using (Figure9Rule.C4 (g := g) (ι i))
  | C5 i => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using (Figure9Rule.C5 (g := g) (ι i))
  | C6 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C6 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C7 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C7 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C8 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C8 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C9 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C9 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C10 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C10 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C11 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C11 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C12 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C12 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C13 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C13 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C14 i j hij => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C14 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C15 i j k hij hjk hik => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C15 (g := g) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)))
  | C16 i j k hij hjk hik => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C16 (g := g) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)))
  | C17 i j k hij hjk hik => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C17 (g := g) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)))
  | C18 i j k hij hjk hik => simpa only [relabel_nil, relabel_cons, relabel_append, relabel_replicate, relabel_power, relabel_multiplier, relabel_Sexp, relabel_CX, relabel_XC, relabel_SWAP, relabel_CIZ, ← eraseScalar_relabel, Gate.relabel] using
      (Figure9Rule.C18 (g := g) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)))

/-- A wire injection transports derivations when it preserves canonical adjacency. -/
theorem figure9Derives_relabel (ι : Fin m ↪ Fin n)
    (hι : ∀ w : Word m, IsAdjacentWord w → IsAdjacentWord (relabel ι w))
    {u v : Word m} (h : Figure9Derives g u v) :
    Figure9Derives g (relabel ι u) (relabel ι v) := by
  apply h.map (Gate.relabel ι)
  intro u v hr
  refine .rule ⟨?_, hι u hr.2.1, hι v hr.2.2.1, ?_, ?_⟩
  · exact hr.1.elim (fun h => Or.inl (h.relabel ι)) (fun h => Or.inr (h.relabel g ι))
  · change eraseScalar (relabel ι u) = relabel ι u
    rw [eraseScalar_relabel, hr.2.2.2.1]
  · change eraseScalar (relabel ι v) = relabel ι v
    rw [eraseScalar_relabel, hr.2.2.2.2]

/-- Idle-wire insertion on the left is a source presentation operation. -/
theorem figure9Derives_shift {u v : Word n} (h : Figure9Derives g u v) :
    Figure9Derives g (relabel (shiftEmbedding n) u) (relabel (shiftEmbedding n) v) :=
  figure9Derives_relabel g _ (fun _ hw => hw.shift) h

/-- Idle-wire insertion on the right preserves the source relation. -/
theorem figure9Derives_initial {u v : Word n} (h : Figure9Derives g u v) :
    Figure9Derives g (relabel (initialEmbedding n) u) (relabel (initialEmbedding n) v) :=
  figure9Derives_relabel g _ (fun _ hw => hw.initial) h

/-- Two-wire proofs may be placed at any consecutive pair. -/
theorem figure9Derives_pair (i : Fin (n+1)) {u v : Word 2}
    (h : Figure9Derives g u v) :
    Figure9Derives g (relabel (adjacentPairEmbedding i) u)
      (relabel (adjacentPairEmbedding i) v) :=
  figure9Derives_relabel g _ (fun _ hw => hw.relabel_adjacentPair i) h

end QuditClifford.Circuit
