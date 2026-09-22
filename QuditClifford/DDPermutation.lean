import QuditClifford.SymplecticThreeWireB

/-! # Exact permutation of an adjacent D-box pair -/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

/-- The phase core of two D boxes permutes using C13, C14 and controlled-phase
commutation. Both exponents are arbitrary natural numbers. -/
theorem classWord_DD_phase_permute (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (r s : ℕ) :
    classWord g (SWAP (d := d) i j hij) * classWord g (SWAP (d := d) j k hjk) *
        classWord g [.CZ j k hjk] ^r * classWord g (SWAP (d := d) i j hij) *
        classWord g [.CZ i j hij] ^s * classWord g (SWAP (d := d) j k hjk) =
      classWord g (SWAP (d := d) j k hjk) * classWord g [.CZ j k hjk] ^s *
        classWord g (SWAP (d := d) i j hij) * classWord g [.CZ i j hij] ^r := by
  let U := classWord g (SWAP (d := d) i j hij)
  let T := classWord g (SWAP (d := d) j k hjk)
  let Q := classWord g [.CZ j k hjk]
  let R := classWord g [.CZ i j hij]
  let N := classWord g (CIZ (d := d) i j k hij hjk hik)
  have hu : U*U=1 := classWord_SWAP_sq g i j hij
  have ht : T*T=1 := classWord_SWAP_sq g j k hjk
  have hnU : N=U*Q*U⁻¹ := classWord_CIZ_other_conjugate g i j k hij hjk hik
  have hnT : N=T*R*T⁻¹ := classWord_CIZ_conjugate g i j k hij hjk hik
  have hb : U*T*U=T*U*T :=
    (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inr (.C13 i j k hij hjk hik)))
  have hUN : SemiconjBy U N Q := by
    change U*N=Q*U
    rw [hnU, inv_eq_of_mul_eq_one_right hu]
    simp only [← mul_assoc, hu, one_mul]
  have hTN : SemiconjBy T N R := by
    change T*N=R*T
    rw [hnT, inv_eq_of_mul_eq_one_right ht]
    simp only [← mul_assoc, ht, one_mul]
  have hTR : SemiconjBy T R N := by change T*R=N*T; rw [hnT]; group
  have hc : Commute R N := classWord_CZ_first_commute_CIZ g i j k hij hjk hik
  change U*T*Q^r*U*R^s*T=T*Q^s*U*R^r
  calc
    _ = U*T*(U*N^r)*R^s*T := by rw [(hUN.pow_right r).eq]; group
    _ = (U*T*U)*N^r*R^s*T := by group
    _ = T*U*(T*N^r)*R^s*T := by rw [hb]; group
    _ = T*U*(R^r*T)*R^s*T := by rw [(hTN.pow_right r).eq]
    _ = T*U*R^r*(T*R^s)*T := by group
    _ = T*U*R^r*(N^s*T)*T := by rw [(hTR.pow_right s).eq]
    _ = T*U*(R^r*N^s) := by simp only [mul_assoc, ht, mul_one]
    _ = T*U*(N^s*R^r) := by rw [((hc.pow_left r).pow_right s).eq]
    _ = T*(U*N^s)*R^r := by group
    _ = _ := by rw [(hUN.pow_right s).eq]; group

end QuditClifford.Circuit
namespace QuditClifford.NormalBoxes
open Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private def dTail (a b : ZMod d) (i : Fin n) : PresentedCircuit g n :=
  if a=0 then 1 else classWord g [.H i]*classWord g (Sexp i (-b/a))

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem dWord_factor (a b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    classWord g (dWord a b i j hij) =
      classWord g (Circuit.SWAP (d := d) i j hij)*
        classWord g [.CZ i j hij] ^(if a=0 then (-b).val else (-a).val)*dTail g a b j := by
  by_cases ha : a=0 <;> simp only [dWord, dTail, ha, if_true, if_false,
    classWord_append, classWord_replicate, mul_one, mul_assoc]

private theorem dTail_SWAP (a b : ZMod d) (i j : Fin n) (hij : i ≠ j) :
    classWord g (Circuit.SWAP (d := d) i j hij)*dTail g a b j =
      dTail g a b i*classWord g (Circuit.SWAP (d := d) i j hij) := by
  by_cases ha : a=0
  · simp [dTail, ha]
  · simp only [dTail, if_neg ha]
    rw [← mul_assoc, classWord_SWAP_H_right, mul_assoc, classWord_SWAP_Sexp_right]
    group

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem dTail_commute_word (a b : ZMod d) (i : Fin n) (w : Word n)
    (hw : ∀ x ∈ w, i ∉ x.support) : Commute (dTail g a b i) (classWord g w) := by
  by_cases ha : a=0
  · simp only [dTail, if_pos ha]; exact Commute.one_left _
  · have hh := classWord_commute_singleWire g i w [.H 0] hw
    have hs := classWord_commute_singleWire g i w (Sexp 0 (-b/a)) hw
    simp only [relabel, List.map_cons, List.map_nil, Gate.relabel, singleWireEmbedding,
      Function.Embedding.coeFn_mk] at hh
    change Commute (classWord g w) (classWord g [.H i]) at hh
    have hs' : Commute (classWord g w) (classWord g (Sexp i (-b/a))) := by
      simpa only [relabel_Sexp, singleWireEmbedding, Function.Embedding.coeFn_mk] using hs
    simpa only [dTail, if_neg ha] using (hh.mul_right hs').symm

/-- Adjacent D boxes exchange their labels under the two outer SWAPs.
This identity holds exactly, including every scalar in the expanded words. -/
theorem classWord_DD_permute (a b c e : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    classWord g (Circuit.SWAP (d := d) i j hij)*
        classWord g (dWord a b j k hjk ++ dWord c e i j hij)*
        classWord g (Circuit.SWAP (d := d) j k hjk) =
      classWord g (dWord c e j k hjk ++ dWord a b i j hij) := by
  let U := classWord g (Circuit.SWAP (d := d) i j hij)
  let T := classWord g (Circuit.SWAP (d := d) j k hjk)
  let Q := classWord g [.CZ j k hjk]
  let R := classWord g [.CZ i j hij]
  let r := if a=0 then (-b).val else (-a).val
  let s := if c=0 then (-e).val else (-c).val
  let Lk := dTail g a b k
  let Lj := dTail g a b j
  let Mk := dTail g c e k
  let Mj := dTail g c e j
  have hLT : Lk*T=T*Lj := by
    have h := (dTail_SWAP g a b k j hjk.symm).symm
    rw [(classWord_eq_iff_derives g _ _).mpr (derives_SWAP_symmetry g k j hjk.symm)] at h
    exact h
  have hMT : Mj*T=T*Mk := (dTail_SWAP g c e j k hjk).symm
  have hLU : Commute Lk U := by
    apply dTail_commute_word
    intro x hx
    simp only [Circuit.SWAP, List.mem_append, scalar, List.mem_replicate, power, List.mem_flatten] at hx
    rcases hx with ⟨_, rfl⟩ | ⟨w, ⟨_, rfl⟩, hx⟩
    · simp [Gate.support]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [Gate.support, hik.symm, hjk.symm]
  have hLR : Commute Lk R := by
    apply dTail_commute_word
    intro x hx
    have hx' : x = .CZ i j hij := by simpa using hx
    subst x
    simp [Gate.support, hik.symm, hjk.symm]
  have hMU : Commute Mk U := by
    apply dTail_commute_word
    intro x hx
    simp only [Circuit.SWAP, List.mem_append, scalar, List.mem_replicate, power, List.mem_flatten] at hx
    rcases hx with ⟨_, rfl⟩ | ⟨w, ⟨_, rfl⟩, hx⟩
    · simp [Gate.support]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [Gate.support, hik.symm, hjk.symm]
  have hMR : Commute Mk R := by
    apply dTail_commute_word
    intro x hx
    have hx' : x = .CZ i j hij := by simpa using hx
    subst x
    simp [Gate.support, hik.symm, hjk.symm]
  have hLM : Commute Lj Mk := by
    by_cases hc : c=0
    · simp only [Mk, dTail, if_pos hc]; exact Commute.one_right _
    · dsimp [Mk]
      simp only [dTail, if_neg hc]
      apply Commute.mul_right
      · apply dTail_commute_word
        intro x hx
        have hx' : x = .H k := by simpa using hx
        subst x
        simpa [Gate.support] using hjk
      · apply dTail_commute_word
        intro x hx
        have hx' : x = .S k := (List.mem_replicate.mp hx).2
        subst x
        simpa [Gate.support] using hjk
  simp only [classWord_append, dWord_factor]
  change U*(T*Q^r*Lk*(U*R^s*Mj))*T=T*Q^s*Mk*(U*R^r*Lj)
  calc
    _ = U*T*Q^r*(Lk*U)*R^s*(Mj*T) := by group
    _ = U*T*Q^r*(U*Lk)*R^s*(T*Mk) := by rw [hLU.eq, hMT]
    _ = U*T*Q^r*U*(Lk*R^s)*T*Mk := by group
    _ = U*T*Q^r*U*(R^s*Lk)*T*Mk := by rw [(hLR.pow_right s).eq]
    _ = U*T*Q^r*U*R^s*(Lk*T)*Mk := by group
    _ = U*T*Q^r*U*R^s*(T*Lj)*Mk := by rw [hLT]
    _ = (U*T*Q^r*U*R^s*T)*(Lj*Mk) := by group
    _ = (T*Q^s*U*R^r)*(Lj*Mk) := by exact congrArg (fun z => z*(Lj*Mk)) (classWord_DD_phase_permute g i j k hij hjk hik r s)
    _ = T*Q^s*U*R^r*(Mk*Lj) := by rw [hLM.eq]
    _ = T*Q^s*U*(R^r*Mk)*Lj := by group
    _ = T*Q^s*U*(Mk*R^r)*Lj := by rw [(hMR.pow_right r).eq]
    _ = T*Q^s*(U*Mk)*R^r*Lj := by group
    _ = _ := by rw [← hMU.eq]; group

/-- Literal-word form of the exact D-pair permutation. -/
theorem derives_DD_permute (a b c e : ZMod d) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    Derives g (Circuit.SWAP (d := d) i j hij ++
      (dWord a b j k hjk ++ dWord c e i j hij) ++ Circuit.SWAP (d := d) j k hjk)
      (dWord c e j k hjk ++ dWord a b i j hij) :=
  (classWord_eq_iff_derives g _ _).mp (classWord_DD_permute g a b c e i j k hij hjk hik)

end QuditClifford.NormalBoxes
