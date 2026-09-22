import QuditClifford.AdjacentTwoWireRewrites
import QuditClifford.AdjacentNormalCircuit

/-!
# Three-wire transport inside the adjacent presented group

The two canonical neighboring SWAPs implement the three wire permutations.
The third phase location is an expanded remote word. Every equality below
comes from guarded Figure 1 rules and their contextual consequences.
-/
noncomputable section
namespace QuditClifford.Circuit.AdjacentThreeWire
variable {d : ℕ} [NeZero d] (g : (ZMod d)ˣ)

theorem cz01_adj : (Gate.CZ (0 : Fin 3) 1 (by decide)).IsAdjacent := ⟨.CZ 0, rfl⟩
theorem cz12_adj : (Gate.CZ (1 : Fin 3) 2 (by decide)).IsAdjacent := ⟨.CZ 1, rfl⟩
omit [NeZero d] in
theorem swap01_adj : IsAdjacentWord (SWAP (d := d) (0 : Fin 3) 1 (by decide)) :=
  isAdjacentWord_SWAP 0 1 (by decide) cz01_adj
omit [NeZero d] in
theorem swap12_adj : IsAdjacentWord (SWAP (d := d) (1 : Fin 3) 2 (by decide)) :=
  isAdjacentWord_SWAP 1 2 (by decide) cz12_adj
omit [NeZero d] in
theorem remote_adj : IsAdjacentWord (CIZ (d := d) (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)) := by
  simp only [CIZ, isAdjacentWord_append, swap12_adj, isAdjacentWord_cons, cz01_adj,
    isAdjacentWord_nil, and_self]

def swap01 : AdjacentPresentedCircuit g 3 :=
  adjacentClassWord g (SWAP (d := d) (0 : Fin 3) 1 (by decide)) swap01_adj
def swap12 : AdjacentPresentedCircuit g 3 :=
  adjacentClassWord g (SWAP (d := d) (1 : Fin 3) 2 (by decide)) swap12_adj
def phase01 : AdjacentPresentedCircuit g 3 := adjacentClassWord g [.CZ 0 1 (by decide)] (by simp [cz01_adj])
def phase12 : AdjacentPresentedCircuit g 3 := adjacentClassWord g [.CZ 1 2 (by decide)] (by simp [cz12_adj])
def phase02 : AdjacentPresentedCircuit g 3 := swap12 g*phase01 g*swap12 g
def swap02 : AdjacentPresentedCircuit g 3 := swap01 g*swap12 g*swap01 g
def H (i : Fin 3) : AdjacentPresentedCircuit g 3 := adjacentClassWord g [.H i] (by simp)
def S (i : Fin 3) : AdjacentPresentedCircuit g 3 := adjacentClassWord g [.S i] (by simp)
def scalar : AdjacentPresentedCircuit g 3 := adjacentClassWord g [.scalar] (by simp)

def perm01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def perm12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def perm02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2

/-- The remote phase constant is precisely the literal T7 expansion. -/
theorem phase02_classWord : phase02 g =
    adjacentClassWord g (CIZ (d := d) (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)) remote_adj := rfl

theorem swap01_sq : swap01 g*swap01 g=1 :=
  (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap01_adj]) isAdjacentWord_nil).mpr
    (adjacentDerives_SWAP_sq g 0 1 (by decide) cz01_adj)

theorem swap12_sq : swap12 g*swap12 g=1 :=
  (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap12_adj]) isAdjacentWord_nil).mpr
    (adjacentDerives_SWAP_sq g 1 2 (by decide) cz12_adj)

/-- C13, with both displayed sides certified adjacent. -/
theorem braid : swap01 g*swap12 g*swap01 g=swap12 g*swap01 g*swap12 g := by
  exact (adjacentClassWord_eq_iff_derives g _ _
    (by simp [swap01_adj, swap12_adj]) (by simp [swap01_adj, swap12_adj])).mpr
      (.rule ⟨Or.inr (.C13 (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)),
        by simp [swap01_adj, swap12_adj], by simp [swap01_adj, swap12_adj]⟩)

/-- C14 in the adjacent quotient, with its printed orientation retained. -/
theorem phase_transport : swap12 g*swap01 g*phase12 g=phase01 g*swap12 g*swap01 g := by
  exact (adjacentClassWord_eq_iff_derives g _ _
    (by simp [swap01_adj, swap12_adj, cz01_adj, cz12_adj])
    (by simp [swap01_adj, swap12_adj, cz01_adj, cz12_adj])).mpr
      (.rule ⟨Or.inr (.C14 (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)),
        by simp [swap01_adj, swap12_adj, cz01_adj, cz12_adj],
        by simp [swap01_adj, swap12_adj, cz01_adj, cz12_adj]⟩)

variable [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)]

@[simp] theorem swap01_inv : (swap01 g)⁻¹=swap01 g := inv_eq_of_mul_eq_one_right (swap01_sq g)
@[simp] theorem swap12_inv : (swap12 g)⁻¹=swap12 g := inv_eq_of_mul_eq_one_right (swap12_sq g)

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- The two adjacent-SWAP descriptions of the remote CZ coincide by C14. -/
theorem phase02_other : phase02 g=swap01 g*phase12 g*swap01 g := by
  have he := phase_transport g
  calc
    _ = swap12 g*(phase01 g*swap12 g*swap01 g)*swap01 g := by
      dsimp [phase02]
      simp only [mul_assoc, swap01_sq, mul_one]
    _ = swap12 g*(swap12 g*swap01 g*phase12 g)*swap01 g := by rw [he]
    _ = _ := by simp only [← mul_assoc, swap12_sq, one_mul]

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
@[simp] theorem swap02_sq : swap02 g*swap02 g=1 := by
  dsimp [swap02]
  calc
    _ = swap01 g*swap12 g*(swap01 g*swap01 g)*swap12 g*swap01 g := by group
    _ = 1 := by rw [swap01_sq]; simp only [mul_one, mul_assoc, swap12_sq, swap01_sq]

@[simp] theorem swap02_inv : (swap02 g)⁻¹=swap02 g := inv_eq_of_mul_eq_one_right (swap02_sq g)

theorem swap01_conj_phase01 : MulAut.conj (swap01 g) (phase01 g)=phase01 g := by
  have hc := adjacentClassWord_SWAP_commute_CZ g (0 : Fin 3) 1 (by decide) cz01_adj
  change Commute (swap01 g) (phase01 g) at hc
  change swap01 g*phase01 g*(swap01 g)⁻¹=phase01 g
  rw [hc.eq]; group

theorem swap01_conj_phase12 : MulAut.conj (swap01 g) (phase12 g)=phase02 g := by
  simp only [MulAut.conj_apply, swap01_inv, phase02_other]

theorem swap01_conj_phase02 : MulAut.conj (swap01 g) (phase02 g)=phase12 g := by
  rw [phase02_other, MulAut.conj_apply, swap01_inv]
  simp only [← mul_assoc, swap01_sq, one_mul]
  simp only [mul_assoc, swap01_sq, mul_one]

theorem swap12_conj_phase01 : MulAut.conj (swap12 g) (phase01 g)=phase02 g := by
  simp only [MulAut.conj_apply, swap12_inv, phase02]

theorem swap12_conj_phase12 : MulAut.conj (swap12 g) (phase12 g)=phase12 g := by
  have hc := adjacentClassWord_SWAP_commute_CZ g (1 : Fin 3) 2 (by decide) cz12_adj
  change Commute (swap12 g) (phase12 g) at hc
  change swap12 g*phase12 g*(swap12 g)⁻¹=phase12 g
  rw [hc.eq]; group

theorem swap12_conj_phase02 : MulAut.conj (swap12 g) (phase02 g)=phase01 g := by
  rw [phase02, MulAut.conj_apply, swap12_inv]
  simp only [← mul_assoc, swap12_sq, one_mul]
  simp only [mul_assoc, swap12_sq, mul_one]

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem word_single_commute (u : Word 3) (hu : IsAdjacentWord u)
    (a : Gate 3) (ha : a.IsAdjacent) (hdis : ∀ b ∈ u, Disjoint b.support a.support) :
    Commute (adjacentClassWord g u hu) (adjacentClassWord g [a] (by simpa using ha)) := by
  have hd : AdjacentDerives g (u++[a]) ([a]++u) := by
    induction u with
    | nil => exact .refl _
    | cons b u ih =>
      rw [isAdjacentWord_cons] at hu
      have h₁ := (ih hu.2 (fun x hx => hdis x (by simp [hx]))).append_left [b]
      have h₂ := (adjacentDerives_disjoint g b a hu.1 ha (hdis b (by simp))).append_right u
      simpa only [List.singleton_append, List.cons_append, List.nil_append] using h₁.trans h₂
  exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [hu, ha]) (by simp [hu, ha])).mpr hd

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem swap_commute_offwire (i j : Fin 3) (hij : i ≠ j)
    (hadj : (Gate.CZ i j hij).IsAdjacent) (a : Gate 3) (ha : a.IsAdjacent)
    (hi : i ∉ a.support) (hj : j ∉ a.support) :
    Commute (adjacentClassWord g (SWAP (d := d) i j hij) (isAdjacentWord_SWAP i j hij hadj))
      (adjacentClassWord g [a] (by simpa using ha)) := by
  apply word_single_commute g _ (isAdjacentWord_SWAP i j hij hadj) a ha
  intro b hb
  simp only [SWAP, List.mem_append, Circuit.scalar, List.mem_replicate, power, List.mem_flatten] at hb
  rcases hb with ⟨_, rfl⟩ | ⟨w, ⟨_, rfl⟩, hb⟩
  · simp [Gate.support]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · simpa [Gate.support] using And.intro hi hj
    · simpa [Gate.support] using hi
    · simpa [Gate.support] using hj

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
theorem swap01_H (i : Fin 3) : swap01 g*H g i=H g (perm01 i)*swap01 g := by
  fin_cases i
  · change swap01 g*H g 0=H g 1*swap01 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap01_adj])
      (by simp [swap01_adj])).mpr (adjacentDerives_SWAP_H_left g 0 1 (by decide) cz01_adj)
  · change swap01 g*H g 1=H g 0*swap01 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap01_adj])
      (by simp [swap01_adj])).mpr (adjacentDerives_SWAP_H_right g 0 1 (by decide) cz01_adj)
  · change swap01 g*H g 2=H g 2*swap01 g
    exact (swap_commute_offwire g 0 1 (by decide) cz01_adj (.H 2) (Gate.isAdjacent_H 2)
      (by simp [Gate.support]) (by simp [Gate.support])).eq

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
theorem swap12_H (i : Fin 3) : swap12 g*H g i=H g (perm12 i)*swap12 g := by
  fin_cases i
  · change swap12 g*H g 0=H g 0*swap12 g
    exact (swap_commute_offwire g 1 2 (by decide) cz12_adj (.H 0) (Gate.isAdjacent_H 0)
      (by simp [Gate.support]) (by simp [Gate.support])).eq
  · change swap12 g*H g 1=H g 2*swap12 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap12_adj])
      (by simp [swap12_adj])).mpr (adjacentDerives_SWAP_H_left g 1 2 (by decide) cz12_adj)
  · change swap12 g*H g 2=H g 1*swap12 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap12_adj])
      (by simp [swap12_adj])).mpr (adjacentDerives_SWAP_H_right g 1 2 (by decide) cz12_adj)

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
theorem swap01_S (i : Fin 3) : swap01 g*S g i=S g (perm01 i)*swap01 g := by
  fin_cases i
  · change swap01 g*S g 0=S g 1*swap01 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap01_adj])
      (by simp [swap01_adj])).mpr (adjacentDerives_SWAP_S_left g 0 1 (by decide) cz01_adj)
  · change swap01 g*S g 1=S g 0*swap01 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap01_adj])
      (by simp [swap01_adj])).mpr (adjacentDerives_SWAP_S_right g 0 1 (by decide) cz01_adj)
  · change swap01 g*S g 2=S g 2*swap01 g
    exact (swap_commute_offwire g 0 1 (by decide) cz01_adj (.S 2) (Gate.isAdjacent_S 2)
      (by simp [Gate.support]) (by simp [Gate.support])).eq

omit [Fact d.Prime] [Fact (Odd d)] [Fact (orderOf g = d-1)] in
theorem swap12_S (i : Fin 3) : swap12 g*S g i=S g (perm12 i)*swap12 g := by
  fin_cases i
  · change swap12 g*S g 0=S g 0*swap12 g
    exact (swap_commute_offwire g 1 2 (by decide) cz12_adj (.S 0) (Gate.isAdjacent_S 0)
      (by simp [Gate.support]) (by simp [Gate.support])).eq
  · change swap12 g*S g 1=S g 2*swap12 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap12_adj])
      (by simp [swap12_adj])).mpr (adjacentDerives_SWAP_S_left g 1 2 (by decide) cz12_adj)
  · change swap12 g*S g 2=S g 1*swap12 g
    exact (adjacentClassWord_eq_iff_derives g _ _ (by simp [swap12_adj])
      (by simp [swap12_adj])).mpr (adjacentDerives_SWAP_S_right g 1 2 (by decide) cz12_adj)

private theorem conjugate_of_transport {G : Type*} [Group G] (w a b : G) (h : w*a=b*w) :
    MulAut.conj w a=b := by
  change w*a*w⁻¹=b
  rw [h]; group

theorem swap01_conj_H (i : Fin 3) : MulAut.conj (swap01 g) (H g i)=H g (perm01 i) :=
  conjugate_of_transport _ _ _ (swap01_H g i)
theorem swap12_conj_H (i : Fin 3) : MulAut.conj (swap12 g) (H g i)=H g (perm12 i) :=
  conjugate_of_transport _ _ _ (swap12_H g i)
theorem swap01_conj_S (i : Fin 3) : MulAut.conj (swap01 g) (S g i)=S g (perm01 i) :=
  conjugate_of_transport _ _ _ (swap01_S g i)
theorem swap12_conj_S (i : Fin 3) : MulAut.conj (swap12 g) (S g i)=S g (perm12 i) :=
  conjugate_of_transport _ _ _ (swap12_S g i)

theorem swap01_conj_scalar : MulAut.conj (swap01 g) (scalar g)=scalar g := by
  apply conjugate_of_transport
  exact (word_single_commute g _ swap01_adj .scalar Gate.isAdjacent_scalar
    (by intros; simp [Gate.support])).eq

theorem swap12_conj_scalar : MulAut.conj (swap12 g) (scalar g)=scalar g := by
  apply conjugate_of_transport
  exact (word_single_commute g _ swap12_adj .scalar Gate.isAdjacent_scalar
    (by intros; simp [Gate.support])).eq

private theorem conjugate_triple {G : Type*} [Group G] (x y z a : G) :
    MulAut.conj (x*y*z) a=MulAut.conj x (MulAut.conj y (MulAut.conj z a)) := by
  simp only [MulAut.conj_apply]
  group

theorem swap02_conj_H (i : Fin 3) : MulAut.conj (swap02 g) (H g i)=H g (perm02 i) := by
  rw [swap02, conjugate_triple, swap01_conj_H, swap12_conj_H, swap01_conj_H]
  fin_cases i <;> rfl

theorem swap02_conj_S (i : Fin 3) : MulAut.conj (swap02 g) (S g i)=S g (perm02 i) := by
  rw [swap02, conjugate_triple, swap01_conj_S, swap12_conj_S, swap01_conj_S]
  fin_cases i <;> rfl

theorem swap02_conj_scalar : MulAut.conj (swap02 g) (scalar g)=scalar g := by
  rw [swap02, conjugate_triple, swap01_conj_scalar, swap12_conj_scalar, swap01_conj_scalar]

theorem swap02_conj_phase01 : MulAut.conj (swap02 g) (phase01 g)=phase12 g := by
  rw [swap02, conjugate_triple, swap01_conj_phase01, swap12_conj_phase01, swap01_conj_phase02]

theorem swap02_conj_phase12 : MulAut.conj (swap02 g) (phase12 g)=phase01 g := by
  rw [swap02, conjugate_triple, swap01_conj_phase12, swap12_conj_phase02, swap01_conj_phase01]

theorem swap02_conj_phase02 : MulAut.conj (swap02 g) (phase02 g)=phase02 g := by
  rw [swap02, conjugate_triple, swap01_conj_phase02, swap12_conj_phase12, swap01_conj_phase12]

/-- Conjugating the neighboring transposition gives the endpoint transposition. -/
theorem swap01_conj_swap12 : MulAut.conj (swap01 g) (swap12 g)=swap02 g := by
  simp only [MulAut.conj_apply, swap01_inv, swap02]

theorem swap12_conj_swap01 : MulAut.conj (swap12 g) (swap01 g)=swap02 g := by
  simp only [MulAut.conj_apply, swap12_inv, swap02]
  exact (braid g).symm

theorem swap01_conj_swap02 : MulAut.conj (swap01 g) (swap02 g)=swap12 g := by
  rw [swap02, MulAut.conj_apply, swap01_inv]
  simp only [← mul_assoc, swap01_sq, one_mul]
  simp only [mul_assoc, swap01_sq, mul_one]

theorem swap12_conj_swap02 : MulAut.conj (swap12 g) (swap02 g)=swap01 g := by
  rw [swap02, braid, MulAut.conj_apply, swap12_inv]
  simp only [← mul_assoc, swap12_sq, one_mul]
  simp only [mul_assoc, swap12_sq, mul_one]

end QuditClifford.Circuit.AdjacentThreeWire
