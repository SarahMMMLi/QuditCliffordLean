import QuditClifford.Figure9Comparison
import QuditClifford.AdjacentBoxCases
import QuditClifford.AdjacentThreeWireBoxCases

/-!
# All forty-two Appendix F branches derived from Figure 9

These statements use the scalar-free forms of the literal Figure 6 box words.
Every proof transfers an existing source-restricted derivation through the
syntactic eighteen-rule comparison. No semantic completeness premise is used.
-/
noncomputable section
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- Appendix F branch corresponding to `adjacentDerives_A_H_zero`. -/
theorem figure9_A_H_zero (A : ABox (ZMod d))
    (ha : A.a = 0) (i : Fin n) :
    Figure9Derives g
      (eraseScalar (A.toWord i ++ [.H i]))
      (eraseScalar ((A.hadamardZero ha).toWord i)) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_A_H_zero g A ha i))

/-- Appendix F branch corresponding to `adjacentDerives_A_S_nonzero`. -/
theorem figure9_A_S_nonzero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (i : Fin n) :
    Figure9Derives g
      (eraseScalar (A.toWord i ++ [.S i]))
      (eraseScalar ((A.phaseStep ha).toWord i)) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_A_S_nonzero g A ha i))

/-- Appendix F branch corresponding to `adjacentDerives_E_S`. -/
theorem figure9_E_S (b : ZMod d) (i : Fin n) :
    Figure9Derives g
      (eraseScalar (eWord b i ++ [.S i]))
      (eraseScalar (eWord (b-1) i)) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_E_S g b i))

/-- Appendix F branch corresponding to `adjacentSymplectic_A_H_nonzero_zero`. -/
theorem figure9_A_H_nonzero_zero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (hb : A.b = 0) (i : Fin n) :
    Figure9Derives g
      (eraseScalar (A.toWord i ++ [.H i]))
      (eraseScalar (A.hadamardStep.toWord i)) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplectic_A_H_nonzero_zero g A ha hb i)

/-- Appendix F branch corresponding to `adjacentSymplectic_A_S_zero`. -/
theorem figure9_A_S_zero (A : ABox (ZMod d))
    (ha : A.a = 0) (i : Fin n) :
    Figure9Derives g
      (eraseScalar (A.toWord i ++ [.S i]))
      (eraseScalar (Sexp i (A.b⁻¹^2) ++ A.toWord i)) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplectic_A_S_zero g A ha i)

/-- Appendix F branch corresponding to `adjacentSymplectic_A_H_nonzero_nonzero`. -/
theorem figure9_A_H_nonzero_nonzero (A : ABox (ZMod d))
    (ha : A.a ≠ 0) (hb : A.b ≠ 0) (i : Fin n) :
    Figure9Derives g
      (eraseScalar (A.toWord i ++ [.H i]))
      (eraseScalar (Sexp i ((A.a*A.b)⁻¹) ++ A.hadamardStep.toWord i)) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplectic_A_H_nonzero_nonzero g A ha hb i)

/-- Appendix F branch corresponding to `adjacentDerives_A_CZ_zero`. -/
theorem figure9_A_CZ_zero (A : ABox (ZMod d)) (ha : A.a=0) :
    Figure9Derives g
      (eraseScalar (A.toWord (0 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (List.replicate (A.b⁻¹).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++ A.toWord (0 : Fin 2))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_A_CZ_zero g A ha))

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_A_CZ_nonzero`. -/
theorem figure9_A_CZ_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0) :
    Figure9Derives g
      (eraseScalar (A.toWord (0 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar ([.H (1 : Fin 2)] ++ List.replicate (A.a⁻¹).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++ List.replicate 3 (.H (1 : Fin 2)) ++
        bWord A.a A.b (0 : Fin 2) (1 : Fin 2) (by decide) ++ (A.controlledPhaseStep ha).toWord (1 : Fin 2))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_A_CZ_nonzero g A ha)

/-- Appendix F branch corresponding to `adjacentDerives_B_H_zero_zero`. -/
theorem figure9_B_H_zero_zero  :
    Figure9Derives g
      (eraseScalar (bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)]))
      (eraseScalar ([.H (1 : Fin 2)] ++ bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_H_zero_zero g))

/-- Appendix F branch corresponding to `adjacentDerives_B_H_zero_nonzero`. -/
theorem figure9_B_H_zero_nonzero (b : ZMod d) (hb : b ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)]))
      (eraseScalar (bWord b 0 (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_H_zero_nonzero g b hb))

/-- Appendix F branch corresponding to `adjacentDerives_B_H_nonzero_zero`. -/
theorem figure9_B_H_nonzero_zero (a : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord a 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)]))
      (eraseScalar ([.H (1 : Fin 2), .H (1 : Fin 2)] ++ bWord 0 (-a) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_H_nonzero_zero g a ha))

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_B_H_nonzero_nonzero_source`. -/
theorem figure9_B_H_nonzero_nonzero_source (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (0 : Fin 2)]))
      (eraseScalar (Circuit.multiplier (1 : Fin 2) (Units.mk0 (b/a) (div_ne_zero hb ha)) ++ Sexp (1 : Fin 2) (b/a) ++
        bWord b (-a) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_B_H_nonzero_nonzero_source g a b ha hb)

/-- Appendix F branch corresponding to `adjacentDerives_B_S_left_zero`. -/
theorem figure9_B_S_left_zero (b : ZMod d) :
    Figure9Derives g
      (eraseScalar (bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (0 : Fin 2)]))
      (eraseScalar ([.S (1 : Fin 2)] ++ bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_S_left_zero g b))

/-- Appendix F branch corresponding to `adjacentDerives_B_S_left_nonzero`. -/
theorem figure9_B_S_left_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (0 : Fin 2)]))
      (eraseScalar (bWord a (b-a) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_S_left_nonzero g a b ha))

/-- Appendix F branch corresponding to `adjacentDerives_B_S_right_zero_zero`. -/
theorem figure9_B_S_right_zero_zero  :
    Figure9Derives g
      (eraseScalar (bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)]))
      (eraseScalar ([.S (0 : Fin 2)] ++ bWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_S_right_zero_zero g))

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_B_S_right_zero`. -/
theorem figure9_B_S_right_zero (b : ZMod d) :
    Figure9Derives g
      (eraseScalar (bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)]))
      (eraseScalar ([.S (0 : Fin 2)] ++ Sexp (1 : Fin 2) (b*b) ++ List.replicate (-b).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        bWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_B_S_right_zero g b)

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_B_S_right_nonzero`. -/
theorem figure9_B_S_right_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)]))
      (eraseScalar ([.S (0 : Fin 2)] ++ Sexp (1 : Fin 2) (a*a) ++ List.replicate (-a).val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        bWord a b (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_B_S_right_nonzero g a b ha)

/-- Appendix F branch corresponding to `adjacentDerives_D_H_zero_zero`. -/
theorem figure9_D_H_zero_zero  :
    Figure9Derives g
      (eraseScalar (dWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)]))
      (eraseScalar ([.H (0 : Fin 2)] ++ dWord (0 : ZMod d) 0 (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_D_H_zero_zero g))

/-- Appendix F branch corresponding to `adjacentDerives_D_H_zero_nonzero`. -/
theorem figure9_D_H_zero_nonzero (b : ZMod d) (hb : b ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)]))
      (eraseScalar (dWord b 0 (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_D_H_zero_nonzero g b hb))

/-- Appendix F branch corresponding to `adjacentDerives_D_H_nonzero_zero`. -/
theorem figure9_D_H_nonzero_zero (a : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord a 0 (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)]))
      (eraseScalar (List.replicate 2 (.H (0 : Fin 2)) ++ dWord 0 (-a) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_D_H_nonzero_zero g a ha))

/-- Appendix F branch corresponding to `adjacentSymplectic_D_H_nonzero_nonzero_source`. -/
theorem figure9_D_H_nonzero_nonzero_source (a b : ZMod d) (ha : a ≠ 0) (hb : b ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.H (1 : Fin 2)]))
      (eraseScalar (Circuit.multiplier (0 : Fin 2) (Units.mk0 (b/a) (div_ne_zero hb ha)) ++ Sexp (0 : Fin 2) (b/a) ++
        dWord b (-a) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplectic_D_H_nonzero_nonzero_source g a b ha hb)

/-- Appendix F branch corresponding to `adjacentDerives_D_S_right_zero`. -/
theorem figure9_D_S_right_zero (b : ZMod d) :
    Figure9Derives g
      (eraseScalar (dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)]))
      (eraseScalar ([.S (0 : Fin 2)] ++ dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_D_S_right_zero g b))

/-- Appendix F branch corresponding to `adjacentDerives_D_S_right_nonzero`. -/
theorem figure9_D_S_right_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (1 : Fin 2)]))
      (eraseScalar (dWord a (b-a) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_D_S_right_nonzero g a b ha))

/-- Appendix F branch corresponding to `adjacentDerives_D_S_left`. -/
theorem figure9_D_S_left (a b : ZMod d) :
    Figure9Derives g
      (eraseScalar (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.S (0 : Fin 2)]))
      (eraseScalar ([.S (1 : Fin 2)] ++ dWord a b (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_D_S_left g a b))

/-- Appendix F branch corresponding to `adjacentDerives_D_CZ_zero`. -/
theorem figure9_D_CZ_zero (b : ZMod d) :
    Figure9Derives g
      (eraseScalar (dWord 0 b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (dWord 0 (b-1) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_D_CZ_zero g b))

/-- Appendix F branch corresponding to `adjacentSymplectic_D_CZ_nonzero`. -/
theorem figure9_D_CZ_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord a b (0 : Fin 2) (1 : Fin 2) (by decide) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (Sexp (1 : Fin 2) a ++ [.H (0 : Fin 2)] ++ Sexp (0 : Fin 2) (-a⁻¹) ++ inverseWord d [.H (0 : Fin 2)] ++
        dWord a (b-1) (0 : Fin 2) (1 : Fin 2) (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplectic_D_CZ_nonzero g a b ha)

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_AB_CZ_zero_zero`. -/
theorem figure9_AB_CZ_zero_zero (A : ABox (ZMod d)) (ha : A.a = 0)
    (k : ZMod d) :
    Figure9Derives g
      (eraseScalar (bWord 0 k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (Sexp (1 : Fin 2) (-2*k*A.b⁻¹) ++ List.replicate A.b⁻¹.val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        bWord 0 k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_AB_CZ_zero_zero g A ha k)

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_AB_CZ_zero_distinct`. -/
theorem figure9_AB_CZ_zero_distinct (A : ABox (ZMod d)) (ha : A.a=0)
    (c k : ZMod d) (hc : c ≠ 0) (hbc : A.b-c ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord c k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (Circuit.multiplier (1 : Fin 2) ((Units.mk0 (A.b-c) hbc / Units.mk0 A.b (A.b_ne_zero ha))⁻¹) ++
        [.H (1 : Fin 2)] ++ List.replicate A.b⁻¹.val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++ inverseWord d [.H (1 : Fin 2)] ++
        bWord c k (0 : Fin 2) (1 : Fin 2) (by decide) ++ (A.zeroDifferenceStep c hbc).toWord (1 : Fin 2))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_AB_CZ_zero_distinct g A ha c k hc hbc)

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_AB_CZ_collision`. -/
theorem figure9_AB_CZ_collision (A : ABox (ZMod d)) (ha : A.a=0)
    (k : ZMod d) :
    Figure9Derives g
      (eraseScalar (bWord A.b k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (inverseWord d ([.H (1 : Fin 2)] ++ List.replicate A.b⁻¹.val (.CZ (0 : Fin 2) (1 : Fin 2) (by decide)) ++
        List.replicate 3 (.H (1 : Fin 2))) ++ [.H (1 : Fin 2), .H (1 : Fin 2)] ++ (A.collisionStep ha k).toWord (0 : Fin 2))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_AB_CZ_collision g A ha k)

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_AB_CZ_zero_nonzero`. -/
theorem figure9_AB_CZ_zero_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0)
    (k : ZMod d) :
    Figure9Derives g
      (eraseScalar (bWord 0 k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (bWord 0 (k-A.a) (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_AB_CZ_zero_nonzero g A ha k)

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_AB_CZ_nonzero`. -/
theorem figure9_AB_CZ_nonzero (A : ABox (ZMod d)) (ha : A.a ≠ 0)
    (c k : ZMod d) (hc : c ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord c k (0 : Fin 2) (1 : Fin 2) (by decide) ++ A.toWord (1 : Fin 2) ++ [.CZ (0 : Fin 2) (1 : Fin 2) (by decide)]))
      (eraseScalar (inverseWord d [.H (1 : Fin 2)] ++ Sexp (1 : Fin 2) (-A.a/c) ++ [.H (1 : Fin 2)] ++
        bWord c (k-A.a) (0 : Fin 2) (1 : Fin 2) (by decide) ++ (A.nonzeroDifferenceStep ha c).toWord (1 : Fin 2))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_AB_CZ_nonzero g A ha c k hc)

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_AB_CZ_zero_zero_zero`. -/
theorem figure9_AB_CZ_zero_zero_zero (A : ABox (ZMod d)) (ha : A.a = 0) :
    Figure9Derives g
      (eraseScalar (bWord (0 : ZMod d) 0 (0 : Fin 2) 1 (by decide) ++ A.toWord 1 ++ [.CZ 0 1 (by decide)]))
      (eraseScalar (List.replicate A.b⁻¹.val (.CZ 0 1 (by decide)) ++
        bWord (0 : ZMod d) 0 (0 : Fin 2) 1 (by decide) ++ A.toWord 1)) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_AB_CZ_zero_zero_zero g A ha)

/-- Appendix F branch corresponding to `adjacentDerives_B_CZ_lower_zero`. -/
theorem figure9_B_CZ_lower_zero (b : ZMod d) :
    Figure9Derives g
      (eraseScalar (bWord 0 b (0 : Fin 3) 1 (by decide) ++ [.CZ 1 2 (by decide)]))
      (eraseScalar (Circuit.CIZ (d := d) 0 1 2 (by decide) (by decide) (by decide) ++
        List.replicate (-b).val (.CZ 1 2 (by decide)) ++ bWord 0 b (0 : Fin 3) 1 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_CZ_lower_zero g b))

/-- Appendix F branch corresponding to `adjacentDerives_B_CZ_lower_nonzero`. -/
theorem figure9_B_CZ_lower_nonzero (a b : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord a b (0 : Fin 3) 1 (by decide) ++ [.CZ 1 2 (by decide)]))
      (eraseScalar (Circuit.CIZ (d := d) 0 1 2 (by decide) (by decide) (by decide) ++
        List.replicate (-a).val (.CZ 1 2 (by decide)) ++ bWord a b (0 : Fin 3) 1 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_B_CZ_lower_nonzero g a b ha))

/-- Appendix F branch corresponding to `adjacentDerives_DD_CZ_zero_zero`. -/
theorem figure9_DD_CZ_zero_zero (b e : ZMod d) :
    Figure9Derives g
      (eraseScalar (dWord 0 b (1 : Fin 3) 2 (by decide) ++ dWord 0 e 0 1 (by decide) ++ [.CZ 1 2 (by decide)]))
      (eraseScalar ([.CZ 0 1 (by decide)] ++ dWord 0 b (1 : Fin 3) 2 (by decide) ++ dWord 0 e 0 1 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_DD_CZ_zero_zero g b e))

/-- Appendix F branch corresponding to `adjacentDerives_DD_CZ_zero_nonzero`. -/
theorem figure9_DD_CZ_zero_nonzero (b c e : ZMod d) (hc : c ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord 0 b (1 : Fin 3) 2 (by decide) ++ dWord c e 0 1 (by decide) ++ [.CZ 1 2 (by decide)]))
      (eraseScalar ([.H 0, .CZ 0 1 (by decide)] ++ inverseWord d [.H 0] ++
        dWord 0 (b-c) (1 : Fin 3) 2 (by decide) ++ dWord c e 0 1 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_DD_CZ_zero_nonzero g b c e hc))

/-- Appendix F branch corresponding to `adjacentDerives_DD_CZ_nonzero_zero`. -/
theorem figure9_DD_CZ_nonzero_zero (a b e : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord a b (1 : Fin 3) 2 (by decide) ++ dWord 0 e 0 1 (by decide) ++ [.CZ 1 2 (by decide)]))
      (eraseScalar ([.H 1, .CZ 0 1 (by decide)] ++ inverseWord d [.H 1] ++
        dWord a b (1 : Fin 3) 2 (by decide) ++ dWord 0 (e-a) 0 1 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_DD_CZ_nonzero_zero g a b e ha))

/-- Appendix F branch corresponding to `adjacentSymplectic_DD_CZ_nonzero_nonzero`. -/
theorem figure9_DD_CZ_nonzero_nonzero (a b c e : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0) :
    Figure9Derives g
      (eraseScalar (dWord a b (1 : Fin 3) 2 (by decide) ++ dWord c e 0 1 (by decide) ++ [.CZ 1 2 (by decide)]))
      (eraseScalar ([.H 1, .H 0, .CZ 0 1 (by decide)] ++ Sexp 1 (-c/a) ++ inverseWord d [.H 1] ++
        Sexp 0 (-a/c) ++ inverseWord d [.H 0] ++
          dWord a (b-c) (1 : Fin 3) 2 (by decide) ++ dWord c (e-a) 0 1 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplectic_DD_CZ_nonzero_nonzero g a b c e ha hc)

/-- Appendix F branch corresponding to `adjacentDerives_BB_CZ_zero_zero`. -/
theorem figure9_BB_CZ_zero_zero (b e : ZMod d) :
    Figure9Derives g
      (eraseScalar (bWord 0 b (0 : Fin 3) 1 (by decide) ++ bWord 0 e 1 2 (by decide) ++ [.CZ 0 1 (by decide)]))
      (eraseScalar ([.CZ 1 2 (by decide)] ++ bWord 0 b (0 : Fin 3) 1 (by decide) ++ bWord 0 e 1 2 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_BB_CZ_zero_zero g b e))

/-- Appendix F branch corresponding to `adjacentDerives_BB_CZ_zero_nonzero`. -/
theorem figure9_BB_CZ_zero_nonzero (b c e : ZMod d) (hc : c ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord 0 b (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide) ++ [.CZ 0 1 (by decide)]))
      (eraseScalar ([.H 2, .CZ 1 2 (by decide)] ++ inverseWord d [.H 2] ++
        bWord 0 (b-c) (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_BB_CZ_zero_nonzero g b c e hc))

/-- Appendix F branch corresponding to `adjacentDerives_BB_CZ_nonzero_zero`. -/
theorem figure9_BB_CZ_nonzero_zero (a b e : ZMod d) (ha : a ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord a b (0 : Fin 3) 1 (by decide) ++ bWord 0 e 1 2 (by decide) ++ [.CZ 0 1 (by decide)]))
      (eraseScalar ([.H 1, .CZ 1 2 (by decide)] ++ inverseWord d [.H 1] ++
        bWord a b (0 : Fin 3) 1 (by decide) ++ bWord 0 (e-a) 1 2 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentDerives_symplectic g (adjacentDerives_BB_CZ_nonzero_zero g a b e ha))

/-- Appendix F branch corresponding to `adjacentSymplecticDerives_BB_CZ_nonzero_nonzero`. -/
theorem figure9_BB_CZ_nonzero_nonzero (a b c e : ZMod d) (ha : a ≠ 0) (hc : c ≠ 0) :
    Figure9Derives g
      (eraseScalar (bWord a b (0 : Fin 3) 1 (by decide) ++ bWord c e 1 2 (by decide) ++ [.CZ 0 1 (by decide)]))
      (eraseScalar ([.H 1, .H 2, .CZ 1 2 (by decide)] ++ Sexp 1 (-c/a) ++ inverseWord d [.H 1] ++
        Sexp 2 (-a/c) ++ inverseWord d [.H 2] ++
          bWord a (b-c) (0 : Fin 3) 1 (by decide) ++ bWord c (e-a) 1 2 (by decide))) :=
  adjacentSymplecticDerives_figure9 g (adjacentSymplecticDerives_BB_CZ_nonzero_nonzero g a b c e ha hc)

end QuditClifford.NormalBoxes
