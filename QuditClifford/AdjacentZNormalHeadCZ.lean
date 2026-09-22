import QuditClifford.AdjacentZSweepWord
import QuditClifford.AdjacentSweepInfrastructure
import QuditClifford.AdjacentThreeWireBoxCases

/-!
# Pushing the first adjacent CZ through a Z-normal sweep

The terminal A and AB cases use the checked two-wire branches, including
the collision branch that shortens the active sweep. Two or more B boxes
use the four BB branches after disjoint interchange with the remaining tail.
Every emitted word has a certificate in the literal dirty Z-sweep grammar.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private theorem cz01_dirty : IsZSweepWord ([.CZ (0 : Fin 2) 1 (by decide)] : Word 2) :=
  isZSweepWord_CZ 0
private theorem h1_dirty : IsZSweepWord ([.H (1 : Fin 2)] : Word 2) :=
  (isZSweepWord_H _).mpr (by decide)
private theorem cz12_dirty : IsZSweepWord ([.CZ (1 : Fin 3) 2 (by decide)] : Word 3) :=
  isZSweepWord_CZ 1
private theorem h1_three_dirty : IsZSweepWord ([.H (1 : Fin 3)] : Word 3) :=
  (isZSweepWord_H _).mpr (by decide)
private theorem h2_three_dirty : IsZSweepWord ([.H (2 : Fin 3)] : Word 3) :=
  (isZSweepWord_H _).mpr (by decide)

attribute [local simp] cz01_dirty h1_dirty cz12_dirty h1_three_dirty h2_three_dirty
  IsZSweepWord.inverseWord

private theorem headCZ_two (N : ZNormal (ZMod d) 2) :
    ∃ (w : Word 2) (_ : IsZSweepWord w) (N' : ZNormal (ZMod d) 2),
      AdjacentSymplecticDerives g (N.toWord ++ [.CZ 0 1 (by decide)]) (w ++ N'.toWord) := by
  cases N with
  | start A =>
    by_cases ha : A.a=0
    · refine ⟨List.replicate A.b⁻¹.val (.CZ 0 1 (by decide)),
        IsZSweepWord.replicate _ cz01_dirty _, .start A, ?_⟩
      exact adjacentDerives_symplectic g (adjacentDerives_A_CZ_zero g A ha)
    · refine ⟨[.H 1] ++ List.replicate A.a⁻¹.val (.CZ 0 1 (by decide)) ++
          List.replicate 3 (.H 1), ?_, .step A.a A.b (.start (A.controlledPhaseStep ha)), ?_⟩
      · exact (isZSweepWord_append _ _).mpr
          ⟨(isZSweepWord_append _ _).mpr ⟨h1_dirty, IsZSweepWord.replicate _ cz01_dirty _⟩,
            IsZSweepWord.replicate _ h1_dirty _⟩
      · simpa only [ZNormal.toWord, ABox.relabel_toWord, shiftEmbedding,
          Function.Embedding.coeFn_mk, List.append_assoc] using
          adjacentSymplecticDerives_A_CZ_nonzero g A ha
  | step c k T =>
    cases T with
    | start A =>
      by_cases ha : A.a=0
      · by_cases hc : c=0
        · subst c
          refine ⟨Sexp 1 (-2*k*A.b⁻¹) ++ List.replicate A.b⁻¹.val (.CZ 0 1 (by decide)),
            (isZSweepWord_append _ _).mpr ⟨isZSweepWord_Sexp _ _,
              IsZSweepWord.replicate _ cz01_dirty _⟩, .step 0 k (.start A), ?_⟩
          simpa only [ZNormal.toWord, ABox.relabel_toWord, shiftEmbedding,
            Function.Embedding.coeFn_mk, List.append_assoc] using
            adjacentSymplecticDerives_AB_CZ_zero_zero g A ha k
        · by_cases hbc : A.b-c=0
          · have hc' : c=A.b := (sub_eq_zero.mp hbc).symm
            subst c
            refine ⟨inverseWord d ([.H 1] ++
                List.replicate A.b⁻¹.val (.CZ 0 1 (by decide)) ++ List.replicate 3 (.H 1)) ++
                [.H 1, .H 1], ?_, .start (A.collisionStep ha k), ?_⟩
            · apply (isZSweepWord_append _ _).mpr
              constructor
              · apply IsZSweepWord.inverseWord
                exact (isZSweepWord_append _ _).mpr
                  ⟨(isZSweepWord_append _ _).mpr ⟨h1_dirty, IsZSweepWord.replicate _ cz01_dirty _⟩,
                    IsZSweepWord.replicate _ h1_dirty _⟩
              · exact (isZSweepWord_append [.H 1] [.H 1]).mpr ⟨h1_dirty, h1_dirty⟩
            · simpa only [ZNormal.toWord, ABox.relabel_toWord, shiftEmbedding,
                Function.Embedding.coeFn_mk, List.append_assoc] using
                adjacentSymplecticDerives_AB_CZ_collision g A ha k
          · refine ⟨Circuit.multiplier 1
                ((Units.mk0 (A.b-c) hbc / Units.mk0 A.b (A.b_ne_zero ha))⁻¹) ++ [.H 1] ++
                List.replicate A.b⁻¹.val (.CZ 0 1 (by decide)) ++ inverseWord d [.H 1],
              ?_, .step c k (.start (A.zeroDifferenceStep c hbc)), ?_⟩
            · simp only [isZSweepWord_append]
              exact ⟨⟨⟨isZSweepWord_multiplier _ _ (by decide), h1_dirty⟩,
                IsZSweepWord.replicate _ cz01_dirty _⟩, h1_dirty.inverseWord⟩
            · simpa only [ZNormal.toWord, ABox.relabel_toWord, shiftEmbedding,
                Function.Embedding.coeFn_mk, List.append_assoc] using
                adjacentSymplecticDerives_AB_CZ_zero_distinct g A ha c k hc hbc
      · by_cases hc : c=0
        · subst c
          refine ⟨[], isZSweepWord_nil, .step 0 (k-A.a) (.start A), ?_⟩
          simpa only [ZNormal.toWord, ABox.relabel_toWord, shiftEmbedding,
            Function.Embedding.coeFn_mk, List.append_assoc, List.nil_append] using
            adjacentSymplecticDerives_AB_CZ_zero_nonzero g A ha k
        · refine ⟨inverseWord d [.H 1] ++ Sexp 1 (-A.a/c) ++ [.H 1], ?_,
            .step c (k-A.a) (.start (A.nonzeroDifferenceStep ha c)), ?_⟩
          · exact (isZSweepWord_append _ _).mpr
              ⟨(isZSweepWord_append _ _).mpr ⟨h1_dirty.inverseWord, isZSweepWord_Sexp _ _⟩, h1_dirty⟩
          · simpa only [ZNormal.toWord, ABox.relabel_toWord, shiftEmbedding,
              Function.Embedding.coeFn_mk, List.append_assoc] using
              adjacentSymplecticDerives_AB_CZ_nonzero g A ha c k hc

private def extendPairNormal (n : ℕ) : ZNormal (ZMod d) 2 → ZNormal (ZMod d) (n+2)
  | .start A => .start A
  | .step a b (.start A) => .step a b (.start A)

omit [NeZero d] [Fact (Odd d)] in
private theorem extendPairNormal_toWord (n : ℕ) (N : ZNormal (ZMod d) 2) :
    (extendPairNormal n N).toWord =
      relabel (adjacentPairEmbedding (0 : Fin (n+1))) N.toWord := by
  cases N with
  | start A => simp [extendPairNormal, ZNormal.toWord, ABox.relabel_toWord]
  | step a b N =>
    cases N with
    | start A =>
      simp only [extendPairNormal, ZNormal.toWord, relabel_append, relabel_bWord,
        ABox.relabel_toWord, shiftEmbedding, Function.Embedding.coeFn_mk,
        adjacentPairEmbedding_zero, adjacentPairEmbedding_one]
      rfl

private theorem headCZ_two_embed (n : ℕ) (N : ZNormal (ZMod d) 2) :
    ∃ (r : ZSweepWord (n+1)) (N' : ZNormal (ZMod d) (n+2)),
      AdjacentSymplecticDerives g
        ((extendPairNormal n N).toWord ++ [.CZ 0 1 (adjacent_ne (0 : Fin (n+1)))])
        (r.toWord ++ N'.toWord) := by
  obtain ⟨w, hw, M, h⟩ := headCZ_two g N
  obtain ⟨r, hr⟩ := (isZSweepWord_iff_exists _).mp (hw.relabel_pair (n := n))
  refine ⟨r, extendPairNormal n M, ?_⟩
  have ht := adjacentSymplecticDerives_pair g (0 : Fin (n+1)) h
  simpa only [relabel_append, relabel_cons, relabel_nil, Gate.relabel,
    adjacentPairEmbedding_zero, adjacentPairEmbedding_one, ← hr, ← extendPairNormal_toWord] using ht

private theorem bb_headCZ (a b c e : ZMod d) :
    ∃ w : Word 3, IsZSweepWord w ∧ AdjacentSymplecticDerives g
      (bWord a b (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide) ++ [.CZ 0 1 (by decide)])
      (w ++ bWord a (b-c) 0 1 (by decide) ++ bWord c (e-a) 1 2 (by decide)) := by
  by_cases ha : a=0
  · subst a
    by_cases hc : c=0
    · subst c
      refine ⟨[.CZ 1 2 (by decide)], cz12_dirty, ?_⟩
      simpa only [sub_zero] using
        adjacentDerives_symplectic g (adjacentDerives_BB_CZ_zero_zero g b e)
    · refine ⟨[.H 2, .CZ 1 2 (by decide)] ++ inverseWord d [.H 2], ?_, ?_⟩
      · exact (isZSweepWord_append _ _).mpr
          ⟨(isZSweepWord_append [.H 2] [.CZ 1 2 (by decide)]).mpr ⟨h2_three_dirty, cz12_dirty⟩,
            h2_three_dirty.inverseWord⟩
      · simpa only [sub_zero] using
          adjacentDerives_symplectic g (adjacentDerives_BB_CZ_zero_nonzero g b c e hc)
  · by_cases hc : c=0
    · subst c
      refine ⟨[.H 1, .CZ 1 2 (by decide)] ++ inverseWord d [.H 1], ?_, ?_⟩
      · exact (isZSweepWord_append _ _).mpr
          ⟨(isZSweepWord_append [.H 1] [.CZ 1 2 (by decide)]).mpr ⟨h1_three_dirty, cz12_dirty⟩,
            h1_three_dirty.inverseWord⟩
      · simpa only [sub_zero] using
          adjacentDerives_symplectic g (adjacentDerives_BB_CZ_nonzero_zero g a b e ha)
    · refine ⟨[.H 1, .H 2, .CZ 1 2 (by decide)] ++ Sexp 1 (-c/a) ++
          inverseWord d [.H 1] ++ Sexp 2 (-a/c) ++ inverseWord d [.H 2], ?_, ?_⟩
      · simp only [isZSweepWord_append]
        refine ⟨⟨⟨⟨?_, isZSweepWord_Sexp _ _⟩, h1_three_dirty.inverseWord⟩,
          isZSweepWord_Sexp _ _⟩, h2_three_dirty.inverseWord⟩
        exact (isZSweepWord_append [.H 1] [.H 2, .CZ 1 2 (by decide)]).mpr
          ⟨h1_three_dirty,
            (isZSweepWord_append [.H 2] [.CZ 1 2 (by decide)]).mpr ⟨h2_three_dirty, cz12_dirty⟩⟩
      · exact adjacentSymplecticDerives_BB_CZ_nonzero_nonzero g a b c e ha hc

set_option linter.unusedSectionVars false in
private theorem headCZ_tail_interchange {n : ℕ} (w : Word n) (hw : IsAdjacentWord w) :
    AdjacentDerives g
      (relabel (shiftEmbedding (n+1)) (relabel (shiftEmbedding n) w) ++
        [.CZ 0 1 (adjacent_ne (0 : Fin (n+1)))])
      ([.CZ 0 1 (adjacent_ne (0 : Fin (n+1)))] ++
        relabel (shiftEmbedding (n+1)) (relabel (shiftEmbedding n) w)) := by
  have hd : ∀ i : Fin n, ∀ j : Fin 2,
      ((shiftEmbedding n).trans (shiftEmbedding (n+1))) i ≠
        adjacentPairEmbedding (0 : Fin (n+1)) j := by
    intro i j h
    have hv := congrArg Fin.val h
    fin_cases j <;> simp [shiftEmbedding, adjacentPairEmbedding] at hv
  have ht := adjacentDerives_relabel_interchange g
    ((shiftEmbedding n).trans (shiftEmbedding (n+1)))
    (adjacentPairEmbedding (0 : Fin (n+1))) hd w [.CZ 0 1 (by decide)]
    (by simpa only [relabel_trans] using hw.shift.shift)
    ((show IsAdjacentWord ([.CZ (0 : Fin 2) 1 (by decide)] : Word 2) from
      by simpa using (Gate.isAdjacent_CZ (0 : Fin 1) (by decide))).relabel_adjacentPair 0)
  simpa only [relabel_trans, relabel_cons, relabel_nil, Gate.relabel,
    adjacentPairEmbedding_zero, adjacentPairEmbedding_one] using ht

/-- A CZ on the first adjacent pair crosses every Z-normal sweep. The
residual is explicitly a dirty Z-sweep word, including both collision and
two-B cases of the recursive grammar. -/
theorem ZNormal.adjacentSymplecticDerives_pushHeadCZ {n : ℕ}
    (N : ZNormal (ZMod d) (n+2)) :
    ∃ (r : ZSweepWord (n+1)) (N' : ZNormal (ZMod d) (n+2)),
      AdjacentSymplecticDerives g
        (N.toWord ++ [.CZ 0 1 (adjacent_ne (0 : Fin (n+1)))])
        (r.toWord ++ N'.toWord) := by
  cases N with
  | start A => exact headCZ_two_embed g n (.start A)
  | step a b T =>
    cases T with
    | start A => exact headCZ_two_embed g n (.step a b (.start A))
    | @step m c e N =>
      obtain ⟨w, hw, h⟩ := bb_headCZ g a b c e
      obtain ⟨r, hr⟩ := (isZSweepWord_iff_exists _).mp (hw.relabel_triple (n := m))
      refine ⟨r, .step a (b-c) (.step c (e-a) N), ?_⟩
      have ht := adjacentSymplecticDerives_triple g (0 : Fin (m+1)) h
      simp only [relabel_append, relabel_bWord, relabel_cons, relabel_nil, Gate.relabel,
        adjacentTripleEmbedding_zero, adjacentTripleEmbedding_one, adjacentTripleEmbedding_two,
        ← hr] at ht
      have hc := adjacentDerives_symplectic g (headCZ_tail_interchange g N.toWord N.toWord_isAdjacent)
      have h₁ := hc.append_left
        (bWord a b (0 : Fin (m+3)) 1 (adjacent_ne (0 : Fin (m+2))) ++
          bWord c e 1 2 (adjacent_ne (1 : Fin (m+2))))
      have h₂ := ht.append_right
        (relabel (shiftEmbedding (m+2)) (relabel (shiftEmbedding (m+1)) N.toWord))
      simp only [List.append_assoc] at h₁ h₂
      simpa only [ZNormal.toWord, relabel_append, relabel_bWord, shiftEmbedding,
        Function.Embedding.coeFn_mk, List.append_assoc] using h₁.trans h₂

end QuditClifford.NormalBoxes
