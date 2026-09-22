import QuditClifford.Figure9TwoWire
import QuditClifford.AdjacentCompleteness

/-!
# Syntactic comparison with the completed adjacent presentation

Every erased Figure 1 derivation is replayed using Figure 9's eighteen
relations. The Pauli deletions are theorems of those relations. The reverse
comparison does not assume semantic completeness of Figure 9.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private theorem figure1Rule_figure9 {u v : Word n} (hr : Figure1Rule g u v)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) := by
  cases hr with
  | C0 => simp; exact .refl _
  | C1 i =>
    simpa using figure9Derives_rule (Figure9Rule.C1 (g := g) i) hu hv
  | C2 i =>
    simpa using figure9Derives_rule (Figure9Rule.C2 (g := g) i) hu (by simpa using hv.eraseScalar)
  | C3 i k =>
    simpa using figure9Derives_rule (Figure9Rule.C3 (g := g) i k)
      (by simpa using hu.eraseScalar) (by simpa using hv.eraseScalar)
  | C4 i =>
    have h := figure9Derives_rule (Figure9Rule.C4 (g := g) i)
      (by simpa using hu.eraseScalar) ((isAdjacentWord_append _ _).mpr
        ⟨isAdjacentWord_Sexp _ _, (isAdjacentWord_multiplier i g).eraseScalar⟩)
    have hz := (figure9Derives_Zexp g i ((1-(g : ZMod d)) * (2*(g : ZMod d)^2)⁻¹)).append_right
      (Sexp i ((↑g⁻¹ : ZMod d)^2) ++ eraseScalar (multiplier i g))
    exact (by simpa only [eraseScalar_append, eraseScalar_Zexp, eraseScalar_Sexp,
      eraseScalar_S_cons, eraseScalar_nil, List.nil_append, List.append_assoc] using h.trans hz.symm)
  | C5 i =>
    simpa using figure9Derives_rule (Figure9Rule.C5 (g := g) i) hu hv
  | C6 i j hij =>
    simpa using figure9Derives_rule (Figure9Rule.C6 (g := g) i j hij) hu hv
  | C7 i j hij =>
    simpa using figure9Derives_rule (Figure9Rule.C7 (g := g) i j hij)
      (by simpa using hu.eraseScalar) hv
  | C8 i j hij =>
    simpa using figure9Derives_rule (Figure9Rule.C8 (g := g) i j hij) hu hv
  | C9 i j hij =>
    simpa using figure9Derives_rule (Figure9Rule.C9 (g := g) i j hij)
      (by simpa using hu.eraseScalar) (by simpa using hv.eraseScalar)
  | C10 i j hij =>
    simpa using figure9Derives_rule (Figure9Rule.C10 (g := g) i j hij)
      (by simpa using hu.eraseScalar) (by simpa using hv.eraseScalar)
  | C11 i j hij =>
    simpa using figure9Derives_rule (Figure9Rule.C11 (g := g) i j hij)
      (by simpa using hu.eraseScalar) (by simpa using hv.eraseScalar)
  | C12 i j hij =>
    have ha : (Gate.CZ i j hij).IsAdjacent := hv _ (by simp)
    simpa using figure9Derives_figure1_C12 g i j hij ha
  | C13 i j k hij hjk hik =>
    simpa using figure9Derives_rule (Figure9Rule.C16 (g := g) i j k hij hjk hik)
      (by simpa using hu.eraseScalar) (by simpa using hv.eraseScalar)
  | C14 i j k hij hjk hik =>
    simpa using figure9Derives_rule (Figure9Rule.C17 (g := g) i j k hij hjk hik)
      (by simpa using hu.eraseScalar) (by simpa using hv.eraseScalar)
  | C15 i j k hij hjk hik =>
    simpa using figure9Derives_rule (Figure9Rule.C18 (g := g) i j k hij hjk hik)
      (by simpa using hu.eraseScalar) (by simpa using hv.eraseScalar)

set_option linter.unusedSectionVars false in
private theorem structural_figure9 {u v : Word n} (hr : Structural u v)
    (hu : IsAdjacentWord u) (hv : IsAdjacentWord v) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) := by
  cases hr with
  | disjoint a b hab =>
    cases a <;> cases b <;> simp only [eraseScalar_scalar_cons, eraseScalar_H_cons,
      eraseScalar_S_cons, eraseScalar_CZ_cons, eraseScalar_nil]
    all_goals first
      | exact .refl _
      | exact .rule ⟨Or.inl (.disjoint _ _ hab), hu, hv, by simp, by simp⟩
  | CZ_symmetry i j hij =>
    exact .rule ⟨Or.inl (.CZ_symmetry i j hij), hu, hv, by simp, by simp⟩

/-- Every guarded erased Figure 1 step is a consequence of the eighteen source
relations, with its explicit Pauli deletion justified by a Figure 9 proof. -/
theorem adjacentSymplecticRules_figure9 {u v : Word n} (hr : AdjacentSymplecticRules g u v) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) := by
  obtain ⟨hr,hu,hv⟩ := hr
  rcases hr with ((hs|hf)|hs)|⟨i, h, rfl⟩
  · exact structural_figure9 g hs hu hv
  · exact figure1Rule_figure9 g hf hu hv
  · obtain ⟨rfl,rfl⟩ := hs
    exact .refl _
  · rcases h with rfl|rfl
    · simpa using figure9Derives_X g i
    · simpa using figure9Derives_Z g i

/-- The complete erased adjacent derivation transfers syntactically to Figure 9.
This is the missing direction: there is no semantic-equality-to-rule shortcut. -/
theorem adjacentSymplecticDerives_figure9 {u v : Word n}
    (h : AdjacentSymplecticDerives g u v) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) := by
  induction h with
  | refl w => exact .refl _
  | rule h => exact adjacentSymplecticRules_figure9 g h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih => simpa only [eraseScalar_append] using ih.context (eraseScalar l) (eraseScalar r)

/-- Theorem 4.4's completeness direction for the literal corrected eighteen
relations, on every arity of the paper's adjacent primitive alphabet. -/
theorem figure9Complete {u v : Word n} (hu : IsAdjacentWord u) (hv : IsAdjacentWord v)
    (he : ∀ p, symplecticAction d u p = symplecticAction d v p) :
    Figure9Derives g (eraseScalar u) (eraseScalar v) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticErasureComplete g n u v hu hv he)

end QuditClifford.Circuit
