import Mathlib.Tactic.Group

/-!
# Group algebra for the nonzero three-wire box pivot

Every input is an explicit algebraic identity. The circuit application proves
these hypotheses from the syntactic presentation before using the lemma.
-/
namespace QuditClifford.Circuit

/-- Two controlled-addition shears combine their quadratic phase corrections
into the two conjugated factors needed in the D-D box rule. -/
theorem quadratic_box_pivot {G : Type*} [Group G] (X Y Q U V F t s : G)
    (hXQ : X*Q = Q*V*X) (hYQ : Y*Q = Q*U*Y)
    (hYV : Y*V = F^2*V*Y)
    (ht : t*Y*t⁻¹ = F*V*Y) (hs : s*X*s⁻¹ = F*U*X)
    (hYF : Commute Y F) (hYU : Commute Y U)
    (hUF : Commute U F) (hUV : Commute U V) (hVF : Commute V F) :
    Y*X*Q = Q*t*Y*t⁻¹*s*X*s⁻¹ := by
  have hblock : (F*V*Y)*(F*U*X) = U*F^2*V*Y*X := by
    calc
      _ = F*V*(Y*F)*U*X := by group
      _ = F*V*(F*Y)*U*X := by rw [hYF.eq]
      _ = F*(V*F)*(Y*U)*X := by group
      _ = F*(F*V)*(U*Y)*X := by rw [hVF.eq, hYU.eq]
      _ = F^2*(V*U)*Y*X := by rw [pow_two]; group
      _ = F^2*(U*V)*Y*X := by rw [hUV.symm.eq]
      _ = (F^2*U)*V*Y*X := by group
      _ = _ := by rw [(hUF.pow_right 2).symm.eq]
  calc
    Y*X*Q = Y*(X*Q) := by group
    _ = Y*(Q*V*X) := by rw [hXQ]
    _ = (Y*Q)*V*X := by group
    _ = (Q*U*Y)*V*X := by rw [hYQ]
    _ = Q*U*(Y*V)*X := by group
    _ = Q*U*(F^2*V*Y)*X := by rw [hYV]
    _ = Q*(U*F^2*V*Y*X) := by group
    _ = Q*((F*V*Y)*(F*U*X)) := by rw [hblock]
    _ = Q*((t*Y*t⁻¹)*(s*X*s⁻¹)) := by rw [ht, hs]
    _ = _ := by group

end QuditClifford.Circuit
