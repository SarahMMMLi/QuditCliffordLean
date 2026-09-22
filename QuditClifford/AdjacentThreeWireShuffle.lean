import QuditClifford.AdjacentThreeWireSyntax

/-! # Explicit adjacent transpositions for localizing three-wire rule instances -/
namespace QuditClifford.Circuit

def swapThree01 : Fin 3 ↪ Fin 3 := (Equiv.swap 0 1).toEmbedding
def swapThree12 : Fin 3 ↪ Fin 3 := (Equiv.swap 1 2).toEmbedding

/-- A finite sequence of the two adjacent transpositions, in matrix order. -/
def threeShuffle : List Bool → (Fin 3 ↪ Fin 3)
  | [] => Function.Embedding.refl _
  | false::s => (threeShuffle s).trans swapThree01
  | true::s => (threeShuffle s).trans swapThree12

/-- Every ordered pair can be moved to the canonical first adjacent pair. -/
theorem threeShuffle_pair (i j : Fin 3) (hij : i ≠ j) :
    ∃ s : List Bool, threeShuffle s i = 0 ∧ threeShuffle s j = 1 := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals first
    | exact ⟨[], by decide⟩
    | exact ⟨[false], by decide⟩
    | exact ⟨[true], by decide⟩
    | exact ⟨[false,true], by decide⟩
    | exact ⟨[true,false], by decide⟩
    | exact ⟨[false,true,false], by decide⟩

/-- The unused third wire necessarily moves to position two. -/
theorem threeShuffle_triple (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ s : List Bool, threeShuffle s i = 0 ∧ threeShuffle s j = 1 ∧ threeShuffle s k = 2 := by
  obtain ⟨s, hi, hj⟩ := threeShuffle_pair i j hij
  refine ⟨s, hi, hj, ?_⟩
  have hk0 : threeShuffle s k ≠ 0 := by
    intro h
    exact hik ((threeShuffle s).injective (hi.trans h.symm))
  have hk1 : threeShuffle s k ≠ 1 := by
    intro h
    exact hjk ((threeShuffle s).injective (hj.trans h.symm))
  have hv := (threeShuffle s k).isLt
  apply Fin.ext
  have hn0 : (threeShuffle s k).val ≠ 0 := fun h => hk0 (Fin.ext h)
  have hn1 : (threeShuffle s k).val ≠ 1 := fun h => hk1 (Fin.ext h)
  omega

@[simp] theorem relabel_refl {n : ℕ} (w : Word n) : relabel (Function.Embedding.refl _) w = w := by
  unfold relabel
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, ih]
    congr 1
    cases a <;> rfl

/-- The order of embedding composition agrees with actual named-wire relabeling. -/
theorem relabel_trans {l m n : ℕ} (ι : Fin l ↪ Fin m) (κ : Fin m ↪ Fin n) (w : Word l) :
    relabel (ι.trans κ) w = relabel κ (relabel ι w) := by
  unfold relabel
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  cases a <;> rfl

end QuditClifford.Circuit
