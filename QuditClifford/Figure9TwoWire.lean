import QuditClifford.Figure9PauliErasure

/-! # Recovering Figure 1's controlled-phase equation from Figure 9

C13 and C14 are transported across SWAP using C7 and C10--C12.
Their group calculation gives the controlled-phase decomposition C12 of
Figure 1. This argument uses only the eighteen source equations.
-/
noncomputable section
namespace QuditClifford.Circuit

private theorem phase_decomposition {G : Type*} [Group G] (s t c k : G)
    (hst : Commute s t) (hsc : Commute s c)
    (hks : Commute k s)
    (hkt : k*t*k⁻¹ = s*t*c⁻¹) (hkc : k*c*k⁻¹ = s⁻¹*s⁻¹*c) :
    s⁻¹*t⁻¹*k⁻¹*t*k = c := by
  have h : k*(s*t*c)*k⁻¹ = t := by
    calc
      _ = (k*s*k⁻¹)*(k*t*k⁻¹)*(k*c*k⁻¹) := by group
      _ = s*(s*t*c⁻¹)*(s⁻¹*s⁻¹*c) := by
        rw [hkt, hkc, hks.eq]; group
      _ = (s*s)*(t*c⁻¹)*(s⁻¹*s⁻¹)*c := by group
      _ = (t*c⁻¹)*(s*s)*(s⁻¹*s⁻¹)*c := by
        rw [((hst.mul_right hsc.inv_right).mul_left (hst.mul_right hsc.inv_right)).eq]
      _ = t := by group
  have ht : k⁻¹*t*k = s*t*c := by
    calc
      _ = k⁻¹*(k*(s*t*c)*k⁻¹)*k := by rw [h]
      _ = s*t*c := by group
  calc
    _ = s⁻¹*t⁻¹*(k⁻¹*t*k) := by group
    _ = s⁻¹*t⁻¹*(s*t*c) := by rw [ht]
    _ = s⁻¹*(t⁻¹*s)*t*c := by group
    _ = s⁻¹*(s*t⁻¹)*t*c := by rw [hst.inv_right.eq]
    _ = c := by group

variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev h (i : Fin n) : Figure9Presented g n := figure9ClassWord g [.H i] (by simp)
private abbrev s (i : Fin n) : Figure9Presented g n := figure9ClassWord g [.S i] (by simp)
private abbrev c (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    Figure9Presented g n := figure9ClassWord g [.CZ i j hij] (by simp [ha])

private theorem adjCX (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    IsAdjacentWord (CX i j hij) := by simp [CX, ha]
private theorem adjXC (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    IsAdjacentWord (XC i j hij) := by simp [XC, ha]
omit [NeZero d] [Fact d.Prime] [Fact (Odd d)] in
private theorem adjW (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    IsAdjacentWord (SWAP (d := d) i j hij) := by
  apply (isAdjacentWord_append _ _).mpr
  exact ⟨by simp, IsAdjacentWord.power (by simp [ha]) 3⟩

private abbrev w (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    Figure9Presented g n := figure9ClassWord g (SWAP (d := d) i j hij) (adjW i j hij ha)
private abbrev k (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    Figure9Presented g n := figure9ClassWord g (CX i j hij) (adjCX i j hij ha)
private abbrev r (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    Figure9Presented g n := figure9ClassWord g (XC i j hij) (adjXC i j hij ha)

private theorem h_inv (i : Fin n) : (h g i)⁻¹ = h g i^3 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact figure9ClassWord_H_four g i

private theorem k_expand (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    k g i j hij ha = (h g j)⁻¹ * c g i j hij ha * h g j := by
  rw [h_inv]; rfl
private theorem r_expand (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    r g i j hij ha = (h g i)⁻¹ * c g i j hij ha * h g i := by
  rw [h_inv]; rfl

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem c_order (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    c g i j hij ha ^ d = 1 := by
  have hd := figure9Derives_rule (Figure9Rule.C6 (g := g) i j hij)
    (IsAdjacentWord.replicate ha d) (by simp)
  have he := figure9ClassWord_eq_of_derives g
    (IsAdjacentWord.replicate ha d) (by simp) hd
  simpa only [figure9ClassWord_replicate g (.CZ i j hij) ha d,
    figure9ClassWord_nil, c] using he

private theorem c_prev (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    c g i j hij ha ^ (d-1) = (c g i j hij ha)⁻¹ := by
  apply mul_right_cancel (b := c g i j hij ha)
  rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos d), c_order, inv_mul_cancel]

private theorem s_neg (i : Fin n) :
    figure9ClassWord g (Sexp i (-1 : ZMod d)) (by simp) = (s g i)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  have he := figure9ClassWord_Sexp_add g i (-1 : ZMod d) 1
  simpa [s] using he.symm

private theorem s_neg_two (i : Fin n) :
    figure9ClassWord g (Sexp i (-2 : ZMod d)) (by simp) = (s g i)⁻¹*(s g i)⁻¹ := by
  have he := figure9ClassWord_Sexp_add g i (-1 : ZMod d) (-1 : ZMod d)
  rw [show (-1 : ZMod d)+(-1) = -2 by ring] at he
  simpa only [s_neg] using he

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem gate_commute (a b : Gate n) (ha : a.IsAdjacent) (hb : b.IsAdjacent)
    (ea : eraseScalar [a] = [a]) (eb : eraseScalar [b] = [b])
    (hd : Disjoint a.support b.support) :
    Commute (figure9ClassWord g [a] (by simp [ha]))
      (figure9ClassWord g [b] (by simp [hb])) := by
  have hr : Figure9Derives g ([a]++[b]) ([b]++[a]) :=
    .rule ⟨Or.inl (.disjoint a b hd), by simp [ha,hb], by simp [ha,hb],
      by simp only [eraseScalar_append,ea,eb], by simp only [eraseScalar_append,ea,eb]⟩
  exact (figure9ClassWord_eq_iff_derives g _ _ (by simp [ha,hb])
    (by simp [ha,hb])).mpr (by simpa only [eraseScalar_append,ea,eb] using hr)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem ss_commute (i j : Fin n) (hij : i ≠ j) : Commute (s g i) (s g j) := by
  apply gate_commute <;> simp [Gate.support, hij, hij.symm]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem hs_commute (i j : Fin n) (hij : i ≠ j) : Commute (h g i) (s g j) := by
  apply gate_commute <;> simp [Gate.support, hij, hij.symm]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem cs_commute (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    Commute (c g i j hij ha) (s g i) := by
  have hd := figure9Derives_rule (Figure9Rule.C8 (g := g) i j hij)
    (by simp [ha]) (by simp [ha])
  exact (figure9ClassWord_eq_iff_derives g _ _ (by simp [ha]) (by simp [ha])).mpr
    (by simpa using hd)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem w_sq (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    w g i j hij ha * w g i j hij ha = 1 := by
  have hd := figure9Derives_rule (Figure9Rule.C7 (g := g) i j hij)
    ((isAdjacentWord_append _ _).mpr ⟨(adjW i j hij ha).eraseScalar,
      (adjW i j hij ha).eraseScalar⟩) (by simp)
  have he := (figure9ClassWord_eq_iff_derives g
    (SWAP (d := d) i j hij ++ SWAP (d := d) i j hij) []
    (by simp [adjW i j hij ha]) (by simp)).mpr (by simpa using hd)
  exact he

private theorem w_inv (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    (w g i j hij ha)⁻¹ = w g i j hij ha := inv_eq_of_mul_eq_one_right (w_sq g i j hij ha)

private theorem conjW_s (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    MulAut.conj (w g i j hij ha) (s g i) = s g j := by
  have hd := figure9Derives_rule (Figure9Rule.C10 (g := g) i j hij)
    (by simp [(adjW i j hij ha).eraseScalar]) (by simp [(adjW i j hij ha).eraseScalar])
  have he := (figure9ClassWord_eq_iff_derives g
    (SWAP (d := d) i j hij ++ [.S i]) ([.S j] ++ SWAP (d := d) i j hij)
    (by simp [adjW i j hij ha]) (by simp [adjW i j hij ha])).mpr (by simpa using hd)
  change w g i j hij ha * s g i = s g j * w g i j hij ha at he
  simp only [MulAut.conj_apply, he, mul_assoc, mul_inv_cancel, mul_one]

private theorem conjW_h (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    MulAut.conj (w g i j hij ha) (h g i) = h g j := by
  have hd := figure9Derives_rule (Figure9Rule.C11 (g := g) i j hij)
    (by simp [(adjW i j hij ha).eraseScalar]) (by simp [(adjW i j hij ha).eraseScalar])
  have he := (figure9ClassWord_eq_iff_derives g
    (SWAP (d := d) i j hij ++ [.H i]) ([.H j] ++ SWAP (d := d) i j hij)
    (by simp [adjW i j hij ha]) (by simp [adjW i j hij ha])).mpr (by simpa using hd)
  change w g i j hij ha * h g i = h g j * w g i j hij ha at he
  simp only [MulAut.conj_apply, he, mul_assoc, mul_inv_cancel, mul_one]

private theorem conjW_c (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    MulAut.conj (w g i j hij ha) (c g i j hij ha) = c g i j hij ha := by
  have hd := figure9Derives_rule (Figure9Rule.C12 (g := g) i j hij)
    (by simp [(adjW i j hij ha).eraseScalar,ha]) (by simp [(adjW i j hij ha).eraseScalar,ha])
  have he := (figure9ClassWord_eq_iff_derives g
    (SWAP (d := d) i j hij ++ [.CZ i j hij]) ([.CZ i j hij] ++ SWAP (d := d) i j hij)
    (by simp [adjW i j hij ha,ha]) (by simp [adjW i j hij ha,ha])).mpr (by simpa using hd)
  change w g i j hij ha * c g i j hij ha = c g i j hij ha * w g i j hij ha at he
  simp only [MulAut.conj_apply, he, mul_assoc, mul_inv_cancel, mul_one]

private theorem conjW_s_right (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    MulAut.conj (w g i j hij ha) (s g j) = s g i := by
  rw [← conjW_s g i j hij ha]
  simp only [MulAut.conj_apply, w_inv]
  calc
    _ = (w g i j hij ha * w g i j hij ha) * s g i *
        (w g i j hij ha * w g i j hij ha) := by group
    _ = s g i := by rw [w_sq]; simp

private theorem conjW_r (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    MulAut.conj (w g i j hij ha) (r g i j hij ha) = k g i j hij ha := by
  rw [r_expand, map_mul, map_mul, map_inv, conjW_h, conjW_c, k_expand]

private theorem cs_right (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    Commute (c g i j hij ha) (s g j) := by
  have he := congrArg (MulAut.conj (w g i j hij ha)) (cs_commute g i j hij ha).eq
  simpa only [map_mul, conjW_c, conjW_s] using he

private theorem rs (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    r g i j hij ha * s g i = s g j * s g i * (c g i j hij ha)⁻¹ * r g i j hij ha := by
  have hd := figure9Derives_rule (Figure9Rule.C13 (g := g) i j hij)
    (by simp [adjXC i j hij ha])
    (by simp [adjXC i j hij ha, IsAdjacentWord.replicate ha])
  have he := figure9ClassWord_eq_of_derives g
    (by simp [adjXC i j hij ha])
    (by simp [adjXC i j hij ha, IsAdjacentWord.replicate ha]) hd
  simp only [figure9ClassWord_append_certified,
    figure9ClassWord_replicate g (.CZ i j hij) ha (d-1)] at he
  change r g i j hij ha * s g i =
    s g j * s g i * c g i j hij ha ^ (d-1) * r g i j hij ha at he
  simpa only [c_prev] using he

private theorem rc (i j : Fin n) (hij : i ≠ j) (ha : (Gate.CZ i j hij).IsAdjacent) :
    r g i j hij ha * c g i j hij ha =
      (s g j)⁻¹*(s g j)⁻¹*c g i j hij ha * r g i j hij ha := by
  have hd := figure9Derives_rule (Figure9Rule.C14 (g := g) i j hij)
    (by simp [adjXC i j hij ha,ha]) (by simp [adjXC i j hij ha,ha])
  have he := figure9ClassWord_eq_of_derives g
    (by simp [adjXC i j hij ha,ha])
    (by simp [adjXC i j hij ha,ha]) hd
  simpa only [figure9ClassWord_append_certified, s_neg_two, r, s, c] using he

/-- Figure 1 C12 follows syntactically from the literal Figure 9 equations. -/
theorem figure9Derives_figure1_C12 (i j : Fin n) (hij : i ≠ j)
    (ha : (Gate.CZ i j hij).IsAdjacent) :
    Figure9Derives g
      (Sexp i (-1 : ZMod d) ++ Sexp j (-1 : ZMod d) ++
        power (CX i j hij) (d-1) ++ [.S j] ++ CX i j hij) [.CZ i j hij] := by
  have hkt := congrArg (MulAut.conj (w g i j hij ha)) (rs g i j hij ha)
  simp only [map_mul, map_inv, conjW_r, conjW_s, conjW_s_right, conjW_c] at hkt
  have hkc := congrArg (MulAut.conj (w g i j hij ha)) (rc g i j hij ha)
  simp only [map_mul, map_inv, conjW_r, conjW_s_right, conjW_c] at hkc
  have hks : Commute (k g i j hij ha) (s g i) := by
    rw [k_expand]
    exact (((hs_commute g j i hij.symm).inv_left).mul_left
      (cs_commute g i j hij ha)).mul_left (hs_commute g j i hij.symm)
  have ht : k g i j hij ha * s g j * (k g i j hij ha)⁻¹ =
      s g i * s g j * (c g i j hij ha)⁻¹ := by rw [hkt]; group
  have hc : k g i j hij ha * c g i j hij ha * (k g i j hij ha)⁻¹ =
      (s g i)⁻¹*(s g i)⁻¹*c g i j hij ha := by rw [hkc]; group
  have he := phase_decomposition (s g i) (s g j) (c g i j hij ha) (k g i j hij ha)
    (ss_commute g i j hij) (cs_commute g i j hij ha).symm
    hks ht hc
  have hkpow : k g i j hij ha^(d-1) = (k g i j hij ha)⁻¹ := by
    rw [k_expand]
    have hp := map_pow (MulAut.conj (h g j)⁻¹) (c g i j hij ha) (d-1)
    simp only [MulAut.conj_apply, inv_inv] at hp
    rw [← hp, c_prev]
    group
  have hadj : IsAdjacentWord
      (Sexp i (-1 : ZMod d) ++ Sexp j (-1 : ZMod d) ++
        power (CX i j hij) (d-1) ++ [.S j] ++ CX i j hij) := by
    simp [adjCX i j hij ha, (adjCX i j hij ha).power]
  have hw := (figure9ClassWord_eq_iff_derives g _ _ hadj (by simp [ha])).mp
    (show figure9ClassWord g _ hadj = figure9ClassWord g [.CZ i j hij] (by simp [ha]) from by
      simpa only [figure9ClassWord_append_certified,
        figure9ClassWord_power g (CX i j hij) (adjCX i j hij ha) (d-1), s_neg, hkpow, s, c, k] using he)
  simpa using hw

end QuditClifford.Circuit
