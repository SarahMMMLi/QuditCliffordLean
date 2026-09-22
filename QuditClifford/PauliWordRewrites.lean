import QuditClifford.PauliWeylRewrites
import QuditClifford.PauliCircuit
import QuditClifford.PresentedPauliNormality

/-!
# Faithful Pauli subgroups inside the genuine Figure 1 presentation

All multiplication laws below are obtained from the primitive rewrite relations.
Matrix interpretation is used only for injectivity, after the homomorphisms have
been constructed syntactically.
-/

noncomputable section
namespace QuditClifford.Circuit

variable {d n : ℕ} [NeZero d]
variable (g : (ZMod d)ˣ)

private theorem gate_word_commute (a : Gate n) (v : Word n)
    (hav : ∀ b ∈ v, Disjoint a.support b.support) :
    Commute (classWord g [a]) (classWord g v) := by
  induction v with
  | nil => simp
  | cons b v ih =>
    rw [show classWord g (b::v) = classWord g [b]*classWord g v from rfl]
    apply Commute.mul_right
    · exact (classWord_eq_iff_derives g _ _).mpr
        (.rule (Or.inl (.disjoint a b (hav b (by simp)))))
    · exact ih (fun c hc => hav c (by simp [hc]))

/-- Disjoint primitive supports suffice for commutation of whole expanded words. -/
theorem classWord_commute_disjoint_words (u v : Word n)
    (huv : ∀ a ∈ u, ∀ b ∈ v, Disjoint a.support b.support) :
    Commute (classWord g u) (classWord g v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [classWord_cons]
    exact (gate_word_commute g a v (huv a (by simp))).mul_left
      (ih (fun a ha b hb => huv a (by simp [ha]) b hb))

private theorem classWord_flatten (ws : List (Word n)) :
    classWord g ws.flatten = (ws.map (classWord g)).prod := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp [ih]

variable [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev O (a : ZMod d) : PresentedCircuit g n := classWord g (omegaPower a)
private abbrev Xp (i : Fin n) (a : ZMod d) : PresentedCircuit g n := classWord g (Xexp i a)
private abbrev Zp (i : Fin n) (a : ZMod d) : PresentedCircuit g n := classWord g (Zexp i a)

omit [NeZero d] [Fact (Odd d)] in
private theorem X_support (i : Fin n) (a : Gate n) (ha : a ∈ X (d := d) i) :
    a.support = {i} := by
  have hh : a = .H i ∨ a = .S i := by
    simp [X, Sexp] at ha
    aesop
  rcases hh with rfl | rfl <;> rfl

omit [NeZero d] [Fact (Odd d)] in
private theorem Z_support (i : Fin n) (a : Gate n) (ha : a ∈ Z (d := d) i) :
    a.support = {i} := by
  have hh : a = .H i ∨ a = .S i := by
    simp [Z, Sexp] at ha
    aesop
  rcases hh with rfl | rfl <;> rfl

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem XX (i j : Fin n) :
    Commute (classWord g (X (d := d) i)) (classWord g (X (d := d) j)) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · apply classWord_commute_disjoint_words
    intro a ha b hb
    rw [X_support i a ha, X_support j b hb]
    simpa using (Ne.symm hij)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem ZZ (i j : Fin n) :
    Commute (classWord g (Z (d := d) i)) (classWord g (Z (d := d) j)) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · apply classWord_commute_disjoint_words
    intro a ha b hb
    rw [Z_support i a ha, Z_support j b hb]
    simpa using (Ne.symm hij)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem ZX_disjoint (i j : Fin n) (hij : i ≠ j) :
    Commute (classWord g (Z (d := d) i)) (classWord g (X (d := d) j)) := by
  apply classWord_commute_disjoint_words
  intro a ha b hb
  rw [Z_support i a ha, X_support j b hb]
  simpa using (Ne.symm hij)

private theorem Xp_add (i : Fin n) (a b : ZMod d) : Xp g i (a+b) = Xp g i a * Xp g i b := by
  simp only [Xp, Xexp, classWord_power, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod (a.val+b.val) (classWord_X_order g i)).symm

private theorem Zp_add (i : Fin n) (a b : ZMod d) : Zp g i (a+b) = Zp g i a * Zp g i b := by
  simp only [Zp, Zexp, classWord_power, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod (a.val+b.val) (classWord_Z_order g i)).symm

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem Xp_Xp (i j : Fin n) (a b : ZMod d) : Commute (Xp g i a) (Xp g j b) := by
  simp only [Xp, Xexp, classWord_power]
  exact ((XX g i j).pow_left _).pow_right _

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem Zp_Zp (i j : Fin n) (a b : ZMod d) : Commute (Zp g i a) (Zp g j b) := by
  simp only [Zp, Zexp, classWord_power]
  exact ((ZZ g i j).pow_left _).pow_right _

private theorem weyl_pow_right (z x : PresentedCircuit g n) (a : ZMod d)
    (h : z*x = O g a*x*z) (k : ℕ) : z*x^k = O g (a*k)*x^k*z := by
  induction k with
  | zero => simp [O]
  | succ k ih =>
    calc
      _ = (z*x^k)*x := by rw [pow_succ, ← mul_assoc]
      _ = O g (a*k)*x^k*(z*x) := by rw [ih]; simp only [mul_assoc]
      _ = O g (a*k)*(x^k*O g a)*x*z := by rw [h]; simp only [mul_assoc]
      _ = (O g (a*k)*O g a)*x^k*x*z := by
        rw [(classWord_omegaPower_commute g a (x^k)).symm.eq]; simp only [mul_assoc]
      _ = _ := by rw [← classWord_omegaPower_add]; simp [Nat.cast_add, mul_add, pow_succ, mul_assoc]

private theorem weyl_pow_left (z x : PresentedCircuit g n) (a : ZMod d)
    (h : z*x = O g a*x*z) (k : ℕ) : z^k*x = O g (k*a)*x*z^k := by
  induction k with
  | zero => simp [O]
  | succ k ih =>
    calc
      _ = z*(z^k*x) := by rw [pow_succ', mul_assoc]
      _ = (z*O g (k*a))*x*z^k := by rw [ih]; simp only [mul_assoc]
      _ = O g (k*a)*(z*x)*z^k := by
        rw [(classWord_omegaPower_commute g (k*a) z).symm.eq]; simp only [mul_assoc]
      _ = (O g (k*a)*O g a)*x*(z*z^k) := by rw [h]; simp only [mul_assoc]
      _ = _ := by rw [← classWord_omegaPower_add]; simp [Nat.cast_add, add_mul, pow_succ', mul_assoc]

private theorem Zp_Xp (i j : Fin n) (b a : ZMod d) :
    Zp g i b * Xp g j a = O g (if i=j then b*a else 0) * Xp g j a * Zp g i b := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, Zp, Xp, Zexp, Xexp, classWord_power]
    have hr := weyl_pow_right g _ _ 1 (classWord_ZX g i) a.val
    have hl := weyl_pow_left g _ _ _ hr b.val
    simpa using hl
  · simp only [hij, ↓reduceIte, O, classWord_omegaPower_zero, one_mul]
    simpa only [Xp, Zp, Xexp, Zexp, classWord_power] using
      (((ZX_disjoint g i j hij).pow_left b.val).pow_right a.val).eq

private def xList (x : Pauli.Basis d n) (is : List (Fin n)) : PresentedCircuit g n :=
  (is.map (fun i => Xp g i (x i))).prod
private def zList (z : Pauli.Basis d n) (is : List (Fin n)) : PresentedCircuit g n :=
  (is.map (fun i => Zp g i (z i))).prod

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem Xp_xList (i : Fin n) (a : ZMod d) (x : Pauli.Basis d n) (is : List (Fin n)) :
    Commute (Xp g i a) (xList g x is) := by
  induction is with
  | nil => simp [xList]
  | cons j is ih => exact (Xp_Xp g i j a (x j)).mul_right ih

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem Zp_zList (i : Fin n) (a : ZMod d) (x : Pauli.Basis d n) (is : List (Fin n)) :
    Commute (Zp g i a) (zList g x is) := by
  induction is with
  | nil => simp [zList]
  | cons j is ih => exact (Zp_Zp g i j a (x j)).mul_right ih

private theorem xList_add (x y : Pauli.Basis d n) (is : List (Fin n)) :
    xList g (x+y) is = xList g x is * xList g y is := by
  induction is with
  | nil => simp [xList]
  | cons i is ih =>
    change Xp g i (x i+y i)*xList g (x+y) is =
      (Xp g i (x i)*xList g x is)*(Xp g i (y i)*xList g y is)
    rw [Xp_add, ih]
    calc
      _ = Xp g i (x i)*(Xp g i (y i)*xList g x is)*xList g y is := by simp only [mul_assoc]
      _ = _ := by rw [(Xp_xList g i (y i) x is).eq]; simp only [mul_assoc]

private theorem zList_add (x y : Pauli.Basis d n) (is : List (Fin n)) :
    zList g (x+y) is = zList g x is * zList g y is := by
  induction is with
  | nil => simp [zList]
  | cons i is ih =>
    change Zp g i (x i+y i)*zList g (x+y) is =
      (Zp g i (x i)*zList g x is)*(Zp g i (y i)*zList g y is)
    rw [Zp_add, ih]
    calc
      _ = Zp g i (x i)*(Zp g i (y i)*zList g x is)*zList g y is := by simp only [mul_assoc]
      _ = _ := by rw [(Zp_zList g i (y i) x is).eq]; simp only [mul_assoc]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
set_option linter.unusedSectionVars false in
private theorem allX_class (x : Pauli.Basis d n) : classWord g (allX x) = xList g x (List.finRange n) := by
  simp [allX, classWord_flatten, List.map_map, xList, Xp, Function.comp_def]
omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
set_option linter.unusedSectionVars false in
private theorem allZ_class (x : Pauli.Basis d n) : classWord g (allZ x) = zList g x (List.finRange n) := by
  simp [allZ, classWord_flatten, List.map_map, zList, Zp, Function.comp_def]

/-- Tensor products of expanded X powers add exponents using only rewrites. -/
theorem classWord_allX_add (x y : Pauli.Basis d n) :
    classWord g (allX (x+y)) = classWord g (allX x)*classWord g (allX y) := by
  simp only [allX_class, xList_add]
/-- Tensor products of expanded Z powers add exponents using only rewrites. -/
theorem classWord_allZ_add (x y : Pauli.Basis d n) :
    classWord g (allZ (x+y)) = classWord g (allZ x)*classWord g (allZ y) := by
  simp only [allZ_class, zList_add]

private theorem Zp_xList (i : Fin n) (b : ZMod d) (x : Pauli.Basis d n) (is : List (Fin n)) :
    Zp g i b * xList g x is =
      O g ((is.map fun j => if i=j then b*x j else 0).sum) * xList g x is * Zp g i b := by
  induction is with
  | nil => simp [xList, O]
  | cons j is ih =>
    change Zp g i b*(Xp g j (x j)*xList g x is) =
      O g ((if i=j then b*x j else 0)+(is.map fun j => if i=j then b*x j else 0).sum) *
        (Xp g j (x j)*xList g x is)*Zp g i b
    calc
      _ = (Zp g i b*Xp g j (x j))*xList g x is := by simp only [mul_assoc]
      _ = O g (if i=j then b*x j else 0)*Xp g j (x j)*(Zp g i b*xList g x is) := by
        rw [Zp_Xp]; simp only [mul_assoc]
      _ = O g (if i=j then b*x j else 0)*(Xp g j (x j)*O g ((is.map fun j => if i=j then b*x j else 0).sum))*
          xList g x is*Zp g i b := by rw [ih]; simp only [mul_assoc]
      _ = _ := by
        rw [(classWord_omegaPower_commute g _ (Xp g j (x j))).symm.eq]
        simp only [O, classWord_omegaPower_add, mul_assoc]

private theorem Zp_allX (i : Fin n) (b : ZMod d) (x : Pauli.Basis d n) :
    Zp g i b*classWord g (allX x) = O g (b*x i)*classWord g (allX x)*Zp g i b := by
  rw [allX_class, Zp_xList]
  congr 2
  simp [List.finRange, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn]

private theorem zList_allX (z x : Pauli.Basis d n) (is : List (Fin n)) :
    zList g z is*classWord g (allX x) =
      O g ((is.map fun i => z i*x i).sum)*classWord g (allX x)*zList g z is := by
  induction is with
  | nil => simp [zList, O]
  | cons i is ih =>
    change (Zp g i (z i)*zList g z is)*classWord g (allX x) =
      O g (z i*x i+(is.map fun i => z i*x i).sum)*classWord g (allX x)*(Zp g i (z i)*zList g z is)
    calc
      _ = Zp g i (z i)*(zList g z is*classWord g (allX x)) := by simp only [mul_assoc]
      _ = (Zp g i (z i)*O g ((is.map fun i => z i*x i).sum))*classWord g (allX x)*zList g z is := by
        rw [ih]; simp only [mul_assoc]
      _ = O g ((is.map fun i => z i*x i).sum)*(Zp g i (z i)*classWord g (allX x))*zList g z is := by
        rw [(classWord_omegaPower_commute g _ (Zp g i (z i))).symm.eq]; simp only [mul_assoc]
      _ = (O g ((is.map fun i => z i*x i).sum)*O g (z i*x i))*classWord g (allX x)*(Zp g i (z i)*zList g z is) := by
        rw [Zp_allX]; simp only [mul_assoc]
      _ = _ := by rw [← classWord_omegaPower_add, add_comm]

/-- Exact block Weyl commutation, proved inside the primitive presentation. -/
theorem classWord_allZ_allX (z x : Pauli.Basis d n) :
    classWord g (allZ z)*classWord g (allX x) =
      classWord g (omegaPower (dot z x))*classWord g (allX x)*classWord g (allZ z) := by
  rw [allZ_class, zList_allX]
  simp [dot, List.finRange, ← List.ofFn_id, List.map_ofFn, List.sum_ofFn]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
@[simp] theorem classWord_allX_zero : classWord g (allX (0 : Pauli.Basis d n)) = 1 := by
  simp [allX_class, xList, Xp, Xexp, classWord_power]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
@[simp] theorem classWord_allZ_zero : classWord g (allZ (0 : Pauli.Basis d n)) = 1 := by
  simp [allZ_class, zList, Zp, Zexp, classWord_power]

/-- Expanded ordinary Pauli words obey their exact Heisenberg multiplication law
inside Figure 1's syntactic quotient. -/
theorem classWord_pauliWord_mul (p q : Pauli d n) :
    classWord g (pauliWord (p*q)) = classWord g (pauliWord p)*classWord g (pauliWord q) := by
  simp only [pauliWord, classWord_append, Pauli.mul_phase, Pauli.mul_x, Pauli.mul_z]
  symm
  calc
    _ = O g p.phase*(classWord g (allX p.x)*classWord g (allZ p.z)*O g q.phase)*
        classWord g (allX q.x)*classWord g (allZ q.z) := by simp only [O, mul_assoc]
    _ = O g p.phase*(O g q.phase*(classWord g (allX p.x)*classWord g (allZ p.z)))*
        classWord g (allX q.x)*classWord g (allZ q.z) := by
      rw [(classWord_omegaPower_commute g q.phase _).symm.eq]
    _ = (O g p.phase*O g q.phase)*classWord g (allX p.x)*
        (classWord g (allZ p.z)*classWord g (allX q.x))*classWord g (allZ q.z) := by
      simp only [mul_assoc]
    _ = O g (p.phase+q.phase)*(classWord g (allX p.x)*O g (dot p.z q.x))*
        classWord g (allX q.x)*classWord g (allZ p.z)*classWord g (allZ q.z) := by
      rw [← classWord_omegaPower_add, classWord_allZ_allX]; simp only [O, mul_assoc]
    _ = (O g (p.phase+q.phase)*O g (dot p.z q.x))*
        (classWord g (allX p.x)*classWord g (allX q.x))*
        (classWord g (allZ p.z)*classWord g (allZ q.z)) := by
      rw [(classWord_omegaPower_commute g (dot p.z q.x) _).symm.eq]; simp only [mul_assoc]
    _ = _ := by rw [← classWord_omegaPower_add, ← classWord_allX_add, ← classWord_allZ_add]

/-- The ordinary finite Heisenberg group embeds by its literal primitive words. -/
def pauliToPresented : Pauli d n →* PresentedCircuit g n where
  toFun p := classWord g (pauliWord p)
  map_one' := by simp [pauliWord]
  map_mul' := classWord_pauliWord_mul g

@[simp] theorem pauliToPresented_apply (p : Pauli d n) :
    pauliToPresented g p = classWord g (pauliWord p) := rfl

@[simp] theorem presentedToGenerated_pauliToPresented (p : Pauli d n) :
    presentedToGenerated Fact.out g (pauliToPresented g p) = pauliToGenerated Fact.out p := rfl

/-- Faithfulness uses soundness and the independently faithful Pauli matrices. -/
theorem pauliToPresented_injective : Function.Injective (pauliToPresented (n := n) g) := by
  intro p q h
  apply pauliToGenerated_injective (show Odd d from Fact.out)
  exact congrArg (presentedToGenerated Fact.out g) h

private abbrev signClass (s : Multiplicative (ZMod 2)) : PresentedCircuit g n :=
  classWord g (scalar (d*(Multiplicative.toAdd s).val))

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
set_option linter.unusedSectionVars false in
private theorem signClass_add (s t : Multiplicative (ZMod 2)) :
    signClass (n := n) g (s*t) = signClass g s*signClass g t := by
  have ht : (classWord (n := n) g [.scalar])^(2*d) = 1 := by
    have he := (classWord_eq_iff_derives g (scalar (n := n) (2*d)) []).mpr
      (.rule (Or.inr Figure1Rule.C0))
    simpa only [scalar, classWord_replicate, classWord_nil] using he
  have hs : ((classWord (n := n) g [.scalar])^d)^2 = 1 := by
    rw [← pow_mul, mul_comm d 2, ht]
  simp only [signClass, scalar, classWord_replicate, pow_mul,
    toAdd_mul, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod ((Multiplicative.toAdd s).val+(Multiplicative.toAdd t).val) hs).symm

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
set_option linter.unusedSectionVars false in
private theorem signClass_commute (s : Multiplicative (ZMod 2)) (q : PresentedCircuit g n) :
    Commute (signClass g s) q := by
  obtain ⟨w, rfl⟩ := classWord_surjective g q
  exact (classWord_eq_iff_derives g _ _).mpr (derives_scalar_commute g _ w)

/-- The independent sign extension also multiplies correctly by primitive rewrites. -/
def signedPauliToPresented : SignedPauli d n →* PresentedCircuit g n where
  toFun p := classWord g (signedPauliWord p)
  map_one' := by simp [signedPauliWord, pauliWord, scalar]
  map_mul' p q := by
    change signClass g (p.1*q.1)*pauliToPresented g (p.2*q.2) =
      (signClass g p.1*pauliToPresented g p.2)*(signClass g q.1*pauliToPresented g q.2)
    rw [signClass_add, map_mul]
    calc
      _ = signClass g p.1*(signClass g q.1*pauliToPresented g p.2)*pauliToPresented g q.2 := by
        simp only [mul_assoc]
      _ = _ := by rw [(signClass_commute g q.1 _).eq]; simp only [mul_assoc]

@[simp] theorem signedPauliToPresented_apply (p : SignedPauli d n) :
    signedPauliToPresented g p = classWord g (signedPauliWord p) := rfl

@[simp] theorem presentedToGenerated_signedPauliToPresented (p : SignedPauli d n) :
    presentedToGenerated Fact.out g (signedPauliToPresented g p) = signedPauliToGenerated Fact.out p := rfl

/-- The selected signed Pauli subgroup is faithful already in the proposed presentation. -/
theorem signedPauliToPresented_injective :
    Function.Injective (signedPauliToPresented (n := n) g) := by
  intro p q h
  apply signedPauliToGenerated_injective (show Odd d from Fact.out)
  exact congrArg (presentedToGenerated Fact.out g) h

/-- Actual contextual normalization of a product of expanded Pauli words. -/
theorem derives_pauliWord_mul (p q : Pauli d n) :
    Derives g (pauliWord p ++ pauliWord q) (pauliWord (p*q)) := by
  apply (classWord_eq_iff_derives g _ _).mp
  exact (classWord_pauliWord_mul g p q).symm

theorem derives_signedPauliWord_mul (p q : SignedPauli d n) :
    Derives g (signedPauliWord p ++ signedPauliWord q) (signedPauliWord (p*q)) := by
  apply (classWord_eq_iff_derives g _ _).mp
  exact (map_mul (signedPauliToPresented g) p q).symm

/-- Syntactic inverse normalization follows from the proved homomorphism law. -/
theorem derives_inverse_pauliWord (p : Pauli d n) :
    Derives g (inverseWord d (pauliWord p)) (pauliWord p⁻¹) := by
  apply (classWord_eq_iff_derives g _ _).mp
  exact (map_inv (pauliToPresented g) p).symm

theorem derives_inverse_signedPauliWord (p : SignedPauli d n) :
    Derives g (inverseWord d (signedPauliWord p)) (signedPauliWord p⁻¹) := by
  apply (classWord_eq_iff_derives g _ _).mp
  exact (map_inv (signedPauliToPresented g) p).symm

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- A tensor word supported on one coordinate reduces to its one-wire word. -/
theorem classWord_allX_single (i : Fin n) (a : ZMod d) :
    classWord g (allX (Pi.single i a)) = classWord g (Xexp i a) := by
  classical
  rw [allX_class, xList, List.prod_map_eq_pow_single i]
  · simp
  · intro j hji _
    simp [Pi.single_eq_of_ne hji, Xp, Xexp, classWord_power]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
theorem classWord_allZ_single (i : Fin n) (a : ZMod d) :
    classWord g (allZ (Pi.single i a)) = classWord g (Zexp i a) := by
  classical
  rw [allZ_class, zList, List.prod_map_eq_pow_single i]
  · simp
  · intro j hji _
    simp [Pi.single_eq_of_ne hji, Zp, Zexp, classWord_power]

@[simp] theorem pauliToPresented_scalar (a : ZMod d) :
    pauliToPresented (n := n) g (Pauli.scalar a) = classWord g (omegaPower a) := by
  simp [pauliToPresented, pauliWord]

@[simp] theorem pauliToPresented_X_single (i : Fin n) (a : ZMod d) :
    pauliToPresented g (Pauli.X (Pi.single i a)) = classWord g (Xexp i a) := by
  simp [pauliToPresented, pauliWord, classWord_allX_single]

@[simp] theorem pauliToPresented_Z_single (i : Fin n) (a : ZMod d) :
    pauliToPresented g (Pauli.Z (Pi.single i a)) = classWord g (Zexp i a) := by
  simp [pauliToPresented, pauliWord, classWord_allZ_single]

@[simp] theorem signedPauliToPresented_one_pair (p : Pauli d n) :
    signedPauliToPresented g (1,p) = pauliToPresented g p := by
  simp [signedPauliToPresented, signedPauliWord, pauliToPresented, scalar]

/-- The abstract signed scalar generator reduces to the literal Figure 1 scalar. -/
@[simp] theorem signedPauliToPresented_scalarGenerator :
    signedPauliToPresented (n := n) g SignedPauli.scalarGenerator = classWord g [.scalar] := by
  have ht : (classWord (n := n) g [.scalar])^(2*d) = 1 := by
    have he := (classWord_eq_iff_derives g (scalar (n := n) (2*d)) []).mpr
      (.rule (Or.inr Figure1Rule.C0))
    simpa only [scalar, classWord_replicate, classWord_nil] using he
  change classWord g (scalar (d*(1 : ZMod 2).val))*pauliToPresented g (Pauli.scalar 1) = _
  rw [pauliToPresented_scalar]
  simp only [ZMod.val_one, mul_one, omegaPower, scalar, classWord_replicate]
  rw [← pow_add, show d+(d+1) = 2*d+1 by omega, pow_add, ht, one_mul, pow_one]

/-- The signed Pauli image is exactly the independently defined subgroup
closure of scalar/X/Z primitive words. -/
theorem signedPauliToPresented_range :
    (signedPauliToPresented (n := n) g).range = presentedPauliSubgroup g := by
  apply le_antisymm
  · rintro q ⟨p, rfl⟩
    exact signedPauliWord_mem_presentedPauliSubgroup g p
  · apply (Subgroup.closure_le _).mpr
    intro q hq
    rcases hq with rfl | ⟨i, rfl | rfl⟩
    · exact ⟨SignedPauli.scalarGenerator, signedPauliToPresented_scalarGenerator g⟩
    · refine ⟨(1, Pauli.X (Pi.single i 1)), ?_⟩
      change signedPauliToPresented g (1, Pauli.X (Pi.single i 1)) = _
      rw [signedPauliToPresented_one_pair, pauliToPresented_X_single]
      simp only [Xexp, classWord_power, ZMod.val_one, pow_one]
    · refine ⟨(1, Pauli.Z (Pi.single i 1)), ?_⟩
      change signedPauliToPresented g (1, Pauli.Z (Pi.single i 1)) = _
      rw [signedPauliToPresented_one_pair, pauliToPresented_Z_single]
      simp only [Zexp, classWord_power, ZMod.val_one, pow_one]

/-- The syntactically defined Pauli subgroup has the exact signed Pauli coordinates. -/
def signedPauliPresentedEquiv : SignedPauli d n ≃* presentedPauliSubgroup (n := n) g :=
  MulEquiv.ofBijective
    ((signedPauliToPresented g).codRestrict (presentedPauliSubgroup g)
      (fun p => signedPauliWord_mem_presentedPauliSubgroup g p))
    ⟨fun p q h => signedPauliToPresented_injective g (congrArg Subtype.val h), by
      intro q
      have hq : q.val ∈ (signedPauliToPresented g).range := by
        rw [signedPauliToPresented_range]; exact q.property
      obtain ⟨p, hp⟩ := hq
      exact ⟨p, Subtype.ext hp⟩⟩

/-- Every word whose class lies in the Pauli subgroup rewrites to a unique
literal signed Pauli word; uniqueness uses independently proved soundness. -/
theorem existsUnique_signedPauliWord (w : Word n)
    (hw : classWord g w ∈ presentedPauliSubgroup g) :
    ∃! p : SignedPauli d n, Derives g w (signedPauliWord p) := by
  rw [← signedPauliToPresented_range] at hw
  obtain ⟨p, hp⟩ := hw
  refine ⟨p, (classWord_eq_iff_derives g _ _).mp hp.symm, ?_⟩
  intro q hq
  apply signedPauliToPresented_injective g
  exact ((classWord_eq_iff_derives g _ _).mpr hq).symm.trans hp.symm

/-- Exact interpretation is injective on the syntactically generated Pauli subgroup. -/
theorem presentedToGenerated_injOn_pauliSubgroup :
    Set.InjOn (presentedToGenerated (n := n) Fact.out g)
      (↑(presentedPauliSubgroup (n := n) g) : Set (PresentedCircuit g n)) := by
  intro a ha b hb hab
  rw [← signedPauliToPresented_range] at ha hb
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨q, rfl⟩ := hb
  have hpq := signedPauliToGenerated_injective (show Odd d from Fact.out) hab
  exact congrArg (signedPauliToPresented g) hpq

/-- The signed Pauli subgroup already has the expected order in the presentation. -/
theorem presentedPauliSubgroup_card :
    Nat.card (presentedPauliSubgroup (n := n) g) = 2*d^(2*n+1) := by
  rw [← Nat.card_congr (signedPauliPresentedEquiv g).toEquiv, Nat.card_eq_fintype_card,
    SignedPauli.card]

end QuditClifford.Circuit
