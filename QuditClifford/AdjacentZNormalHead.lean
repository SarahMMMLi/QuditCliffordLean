import QuditClifford.AdjacentSweepInfrastructure
import QuditClifford.NormalSweepSyntax

/-!
# Pushing head-wire H and S through the literal Z-normal grammar

Every residual is certified by the dirty Z-sweep grammar. The proof combines
actual A/B branch derivations with disjoint-tail commutation and consecutive
pair transport; no equality of exponent actions is used as a rewrite.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private theorem b_head_H (a b : ZMod d) :
    ∃ (r : Word 1) (a' b' : ZMod d), AdjacentSymplecticDerives g
      (bWord a b (0 : Fin 2) 1 (by decide) ++ [.H 0])
      (relabel (singleWireEmbedding 1) r ++ bWord a' b' 0 1 (by decide)) := by
  by_cases ha : a=0
  · subst a
    by_cases hb : b=0
    · subst b
      exact ⟨[.H 0], 0, 0, adjacentDerives_symplectic g (adjacentDerives_B_H_zero_zero g)⟩
    · refine ⟨[], b, 0, ?_⟩
      simpa only [relabel_nil, List.nil_append] using
        adjacentDerives_symplectic g (adjacentDerives_B_H_zero_nonzero g b hb)
  · by_cases hb : b=0
    · subst b
      exact ⟨[.H 0, .H 0], 0, -a,
        adjacentDerives_symplectic g (adjacentDerives_B_H_nonzero_zero g a ha)⟩
    · refine ⟨Circuit.multiplier 0 (Units.mk0 (b/a) (div_ne_zero hb ha)) ++ Sexp 0 (b/a), b, -a, ?_⟩
      simpa only [relabel_append, relabel_multiplier, relabel_Sexp,
        singleWireEmbedding, Function.Embedding.coeFn_mk, List.append_assoc] using
        adjacentSymplecticDerives_B_H_nonzero_nonzero_source g a b ha hb

private theorem b_head_S (a b : ZMod d) :
    ∃ (r : Word 1) (a' b' : ZMod d), AdjacentSymplecticDerives g
      (bWord a b (0 : Fin 2) 1 (by decide) ++ [.S 0])
      (relabel (singleWireEmbedding 1) r ++ bWord a' b' 0 1 (by decide)) := by
  by_cases ha : a=0
  · subst a
    exact ⟨[.S 0], 0, b, adjacentDerives_symplectic g (adjacentDerives_B_S_left_zero g b)⟩
  · refine ⟨[], a, b-a, ?_⟩
    simpa only [relabel_nil, List.nil_append] using
      adjacentDerives_symplectic g (adjacentDerives_B_S_left_nonzero g a b ha)

/-- H at the distinguished first input produces an explicitly allowed dirty
residual and another Z-normal sweep at the same arity. -/
theorem ZNormal.adjacentSymplecticDerives_pushHeadH {n : ℕ}
    (N : ZNormal (ZMod d) (n+1)) :
    ∃ (r : ZSweepWord n) (N' : ZNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [.H 0]) (r.toWord ++ N'.toWord) := by
  cases N with
  | start A =>
    by_cases ha : A.a=0
    · refine ⟨[], .start (A.hadamardZero ha), ?_⟩
      simpa only [ZSweepWord.toWord_nil, List.nil_append, ZNormal.toWord] using
        adjacentDerives_symplectic g (adjacentDerives_A_H_zero g A ha 0)
    · by_cases hb : A.b=0
      · refine ⟨[], .start A.hadamardStep, ?_⟩
        simpa only [ZSweepWord.toWord_nil, List.nil_append, ZNormal.toWord] using
          adjacentSymplectic_A_H_nonzero_zero g A ha hb 0
      · refine ⟨ZSweepWord.firstPhase ((A.a*A.b)⁻¹), .start A.hadamardStep, ?_⟩
        simpa only [ZSweepWord.toWord_firstPhase, ZNormal.toWord] using
          adjacentSymplectic_A_H_nonzero_nonzero g A ha hb 0
  | @step m a b N =>
    obtain ⟨w, a', b', h⟩ := b_head_H g a b
    obtain ⟨r, hr⟩ := (isAdjacentWord_iff_exists _).mp
      (isAdjacentWord_singleWire (0 : Fin (m+1)) w)
    refine ⟨ZSweepWord.fromTail r, .step a' b' N, ?_⟩
    have ht := adjacentSymplecticDerives_pair g (0 : Fin (m+1)) h
    simp only [relabel_append, relabel_bWord, relabel_cons, relabel_nil, Gate.relabel,
      adjacentPairEmbedding_zero, adjacentPairEmbedding_one] at ht
    rw [relabel_pair_singleWire_one, ← hr] at ht
    have hc := adjacentDerives_symplectic g (adjacentDerives_H_head_tail g N.toWord N.toWord_isAdjacent)
    have h₁ := hc.append_left (bWord a b (0 : Fin (m+2)) 1 (adjacent_ne (0 : Fin (m+1))))
    have h₂ := ht.append_right (relabel (shiftEmbedding (m+1)) N.toWord)
    simp only [List.append_assoc] at h₁ h₂
    simpa only [ZNormal.toWord, ZSweepWord.toWord_fromTail, List.append_assoc] using h₁.trans h₂

/-- S at the distinguished first input also preserves the dirty residual grammar. -/
theorem ZNormal.adjacentSymplecticDerives_pushHeadS {n : ℕ}
    (N : ZNormal (ZMod d) (n+1)) :
    ∃ (r : ZSweepWord n) (N' : ZNormal (ZMod d) (n+1)),
      AdjacentSymplecticDerives g (N.toWord ++ [.S 0]) (r.toWord ++ N'.toWord) := by
  cases N with
  | start A =>
    by_cases ha : A.a=0
    · refine ⟨ZSweepWord.firstPhase (A.b⁻¹^2), .start A, ?_⟩
      simpa only [ZSweepWord.toWord_firstPhase, ZNormal.toWord] using
        adjacentSymplectic_A_S_zero g A ha 0
    · refine ⟨[], .start (A.phaseStep ha), ?_⟩
      simpa only [ZSweepWord.toWord_nil, List.nil_append, ZNormal.toWord] using
        adjacentDerives_symplectic g (adjacentDerives_A_S_nonzero g A ha 0)
  | @step m a b N =>
    obtain ⟨w, a', b', h⟩ := b_head_S g a b
    obtain ⟨r, hr⟩ := (isAdjacentWord_iff_exists _).mp
      (isAdjacentWord_singleWire (0 : Fin (m+1)) w)
    refine ⟨ZSweepWord.fromTail r, .step a' b' N, ?_⟩
    have ht := adjacentSymplecticDerives_pair g (0 : Fin (m+1)) h
    simp only [relabel_append, relabel_bWord, relabel_cons, relabel_nil, Gate.relabel,
      adjacentPairEmbedding_zero, adjacentPairEmbedding_one] at ht
    rw [relabel_pair_singleWire_one, ← hr] at ht
    have hc := adjacentDerives_symplectic g (adjacentDerives_S_commute_relabel g
      (shiftEmbedding (m+1)) 0 (fun j => Fin.succ_ne_zero j) N.toWord N.toWord_isAdjacent.shift)
    have h₁ := hc.append_left (bWord a b (0 : Fin (m+2)) 1 (adjacent_ne (0 : Fin (m+1))))
    have h₂ := ht.append_right (relabel (shiftEmbedding (m+1)) N.toWord)
    simp only [List.append_assoc] at h₁ h₂
    simpa only [ZNormal.toWord, ZSweepWord.toWord_fromTail, List.append_assoc] using h₁.trans h₂

end QuditClifford.NormalBoxes
