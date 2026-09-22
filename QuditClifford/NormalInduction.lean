import QuditClifford.NormalCoordinates

/-!
# Linear normal actions and the induction step for symplectic normal forms

The concrete A/B and D/E actions are packaged as linear symplectic equivalences.
A symplectic map fixing the final Z and X restricts to the preceding wires.
These are statements about the concrete exponent actions, not rewrite proofs.
-/

noncomputable section
namespace QuditClifford.NormalBoxes
universe u
variable {K : Type u} [Field K]

/-- The wirewise symplectic form separates exponent vectors. -/
theorem wiresBracket_ext {n : ℕ} (v w : Wires K n)
    (h : ∀ t, wiresBracket v t = wiresBracket w t) : v = w := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    apply ZNormal.wires_ext
    · apply bracket_ext
      intro t
      have hh := h (Fin.cons t 0)
      rw [wiresBracket_expand v, wiresBracket_expand w] at hh
      simpa using hh
    · apply ih
      intro t
      have hh := h (Fin.cons 0 t)
      rw [wiresBracket_expand v, wiresBracket_expand w] at hh
      simpa [bracket] using hh

theorem wiresBracket_add_left {n : ℕ} (v w t : Wires K n) :
    wiresBracket (v + w) t = wiresBracket v t + wiresBracket w t := by
  simp only [wiresBracket, Pi.add_apply, bracket, Prod.fst_add, Prod.snd_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem wiresBracket_smul_left {n : ℕ} (c : K) (v w : Wires K n) :
    wiresBracket (c • v) w = c * wiresBracket v w := by
  simp only [wiresBracket, Pi.smul_apply, bracket, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Preservation of the nondegenerate form implies injectivity. -/
theorem wiresPreserver_injective {n : ℕ} (f : Wires K n → Wires K n)
    (hf : ∀ v w, wiresBracket (f v) (f w) = wiresBracket v w) : Function.Injective f := by
  intro v w h
  apply wiresBracket_ext
  intro t
  rw [← hf v t, ← hf w t, h]

/-- Split the last wire from all preceding wire coordinates. -/
def splitLast (n : ℕ) : Wires K (n + 1) ≃ₗ[K] (Wires K n × Vector K) where
  toFun v := (Fin.init v, v (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv v := Fin.snoc_init_self v
  right_inv p := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Append an idle wire. -/
def initialEmbed (n : ℕ) : Wires K n →ₗ[K] Wires K (n + 1) :=
  (splitLast n).symm.toLinearMap.comp (LinearMap.inl K (Wires K n) (Vector K))

@[simp] theorem initialEmbed_apply {n : ℕ} (v : Wires K n) :
    initialEmbed n v = Fin.snoc v 0 := rfl

@[simp] theorem initialEmbed_init {n : ℕ} (v : Wires K n) :
    Fin.init (initialEmbed n v) = v := by simp

@[simp] theorem initialEmbed_last {n : ℕ} (v : Wires K n) :
    initialEmbed n v (Fin.last n) = 0 := by simp

theorem lastVector_eq_snoc (v : Vector K) (n : ℕ) :
    lastVector v n = Fin.snoc (0 : Wires K n) v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [lastVector_apply]

theorem wiresBracket_expand_last {n : ℕ} (v w : Wires K (n + 1)) :
    wiresBracket v w = wiresBracket (Fin.init v) (Fin.init w) +
      bracket (v (Fin.last n)) (w (Fin.last n)) := by
  simp [wiresBracket, Fin.sum_univ_castSucc, Fin.init]

@[simp] theorem wiresBracket_initialEmbed {n : ℕ} (v w : Wires K n) :
    wiresBracket (initialEmbed n v) (initialEmbed n w) = wiresBracket v w := by
  rw [wiresBracket_expand_last]
  simp [bracket]

@[simp] theorem wiresBracket_last_right {n : ℕ} (v : Wires K (n + 1)) (w : Vector K) :
    wiresBracket v (lastVector w n) = bracket (v (Fin.last n)) w := by
  rw [lastVector_eq_snoc, wiresBracket_expand_last]
  simp

@[simp] theorem wiresBracket_last_left {n : ℕ} (v : Vector K) (w : Wires K (n + 1)) :
    wiresBracket (lastVector v n) w = bracket v (w (Fin.last n)) := by
  rw [lastVector_eq_snoc, wiresBracket_expand_last]
  simp

/-- Embed a one-wire vector on the last wire. -/
def lastEmbed (n : ℕ) : Vector K →ₗ[K] Wires K (n + 1) :=
  (splitLast n).symm.toLinearMap.comp (LinearMap.inr K (Wires K n) (Vector K))

@[simp] theorem lastEmbed_apply {n : ℕ} (v : Vector K) :
    lastEmbed n v = lastVector v n := (lastVector_eq_snoc v n).symm

theorem wire_decomposition {n : ℕ} (v : Wires K (n + 1)) :
    v = initialEmbed n (Fin.init v) + lastVector (v (Fin.last n)) n := by
  rw [lastVector_eq_snoc]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.init]

section FiniteField
variable [Finite K]

/-- On the finite exponent space, an exact symplectic preserver is linear.
The underlying function is unchanged; this packages the already concrete words. -/
def linearizePreserver {n : ℕ} (f : Wires K n → Wires K n)
    (hf : ∀ v w, wiresBracket (f v) (f w) = wiresBracket v w) : Wires K n →ₗ[K] Wires K n where
  toFun := f
  map_add' v w := by
    apply wiresBracket_ext
    intro t
    obtain ⟨s, rfl⟩ := Finite.surjective_of_injective (wiresPreserver_injective f hf) t
    simp only [hf, wiresBracket_add_left]
  map_smul' c v := by
    apply wiresBracket_ext
    intro t
    obtain ⟨s, rfl⟩ := Finite.surjective_of_injective (wiresPreserver_injective f hf) t
    change wiresBracket (f (c • v)) (f s) = wiresBracket (c • f v) (f s)
    simp only [hf, wiresBracket_smul_left]

end FiniteField

/-- A linear symplectic equivalence on the wirewise exponent representation. -/
structure WireSymplectic (n : ℕ) where
  toLinearEquiv : Wires K n ≃ₗ[K] Wires K n
  preserves : ∀ v w, wiresBracket (toLinearEquiv v) (toLinearEquiv w) = wiresBracket v w

instance {n : ℕ} : CoeFun (WireSymplectic (K := K) n) (fun _ => Wires K n → Wires K n) :=
  ⟨fun f => f.toLinearEquiv⟩

namespace WireSymplectic
variable {n : ℕ}

@[ext] theorem ext {f g : WireSymplectic (K := K) n} (h : ∀ v, f v = g v) : f = g := by
  have he : f.toLinearEquiv = g.toLinearEquiv := LinearEquiv.ext h
  cases f
  cases g
  simp_all

@[simp] theorem apply_add (f : WireSymplectic (K := K) n) (v w : Wires K n) :
    f (v + w) = f v + f w := f.toLinearEquiv.map_add v w

@[simp] theorem apply_smul (f : WireSymplectic (K := K) n) (c : K) (v : Wires K n) :
    f (c • v) = c • f v := f.toLinearEquiv.map_smul c v

@[simp] theorem apply_zero (f : WireSymplectic (K := K) n) : f 0 = 0 :=
  f.toLinearEquiv.map_zero

def ofPreserver [Finite K] (f : Wires K n → Wires K n)
    (hf : ∀ v w, wiresBracket (f v) (f w) = wiresBracket v w) : WireSymplectic (K := K) n where
  toLinearEquiv := LinearEquiv.ofInjectiveEndo (linearizePreserver f hf)
    (wiresPreserver_injective f hf)
  preserves := hf

@[simp] theorem ofPreserver_apply [Finite K] (f : Wires K n → Wires K n)
    (hf : ∀ v w, wiresBracket (f v) (f w) = wiresBracket v w) (v : Wires K n) :
    ofPreserver f hf v = f v := rfl

def refl : WireSymplectic (K := K) n where
  toLinearEquiv := LinearEquiv.refl K _
  preserves _ _ := rfl

def comp (f g : WireSymplectic (K := K) n) : WireSymplectic (K := K) n where
  toLinearEquiv := g.toLinearEquiv.trans f.toLinearEquiv
  preserves v w := (f.preserves (g v) (g w)).trans (g.preserves v w)

@[simp] theorem comp_apply (f g : WireSymplectic (K := K) n) (v : Wires K n) :
    f.comp g v = f (g v) := rfl

def symm (f : WireSymplectic (K := K) n) : WireSymplectic (K := K) n where
  toLinearEquiv := f.toLinearEquiv.symm
  preserves v w := by
    have h := f.preserves (f.toLinearEquiv.symm v) (f.toLinearEquiv.symm w)
    simpa using h.symm

@[simp] theorem apply_symm_apply (f : WireSymplectic (K := K) n) (v : Wires K n) :
    f (f.symm v) = v := f.toLinearEquiv.apply_symm_apply v

@[simp] theorem symm_apply_apply (f : WireSymplectic (K := K) n) (v : Wires K n) :
    f.symm (f v) = v := f.toLinearEquiv.symm_apply_apply v

end WireSymplectic

/-- The concrete Z-normal sweep as a linear symplectic equivalence. -/
def ZNormal.equiv [Finite K] {n : ℕ} (N : ZNormal K n) : WireSymplectic (K := K) n :=
  WireSymplectic.ofPreserver N.action N.preserves

/-- The concrete X-normal sweep as a linear symplectic equivalence. -/
def XNormal.equiv [Finite K] {n : ℕ} (N : XNormal K n) : WireSymplectic (K := K) n :=
  WireSymplectic.ofPreserver N.action N.preserves

@[simp] theorem ZNormal.equiv_apply [Finite K] {n : ℕ} (N : ZNormal K n) (v : Wires K n) :
    N.equiv v = N.action v := rfl

@[simp] theorem XNormal.equiv_apply [Finite K] {n : ℕ} (N : XNormal K n) (v : Wires K n) :
    N.equiv v = N.action v := rfl

@[simp] theorem ZNormal.action_add [Finite K] {n : ℕ} (N : ZNormal K n) (v w : Wires K n) :
    N.action (v + w) = N.action v + N.action w := N.equiv.toLinearEquiv.map_add v w

@[simp] theorem ZNormal.action_smul [Finite K] {n : ℕ} (N : ZNormal K n) (c : K) (v : Wires K n) :
    N.action (c • v) = c • N.action v := N.equiv.toLinearEquiv.map_smul c v

@[simp] theorem XNormal.action_add [Finite K] {n : ℕ} (N : XNormal K n) (v w : Wires K n) :
    N.action (v + w) = N.action v + N.action w := N.equiv.toLinearEquiv.map_add v w

@[simp] theorem XNormal.action_smul [Finite K] {n : ℕ} (N : XNormal K n) (c : K) (v : Wires K n) :
    N.action (c • v) = c • N.action v := N.equiv.toLinearEquiv.map_smul c v

namespace WireSymplectic
variable {n : ℕ}

/-- Fixing the last Z/X forces every vector's final coordinates to remain fixed. -/
theorem last_coordinates (f : WireSymplectic (K := K) (n + 1))
    (hz : f (lastVector zVector n) = lastVector zVector n)
    (hx : f (lastVector xVector n) = lastVector xVector n) (v : Wires K (n + 1)) :
    f v (Fin.last n) = v (Fin.last n) := by
  apply Prod.ext
  · have h := f.preserves v (lastVector xVector n)
    rw [hx, wiresBracket_last_right, wiresBracket_last_right] at h
    simpa using h
  · have h := f.preserves v (lastVector zVector n)
    rw [hz, wiresBracket_last_right, wiresBracket_last_right] at h
    simpa [bracket, zVector] using h

/-- The restriction map to the first n wires. -/
def restrictionMap (f : WireSymplectic (K := K) (n + 1)) : Wires K n →ₗ[K] Wires K n :=
  (LinearMap.fst K (Wires K n) (Vector K)).comp
    ((splitLast n).toLinearMap.comp (f.toLinearEquiv.toLinearMap.comp (initialEmbed n)))

@[simp] theorem restrictionMap_apply (f : WireSymplectic (K := K) (n + 1)) (v : Wires K n) :
    f.restrictionMap v = Fin.init (f (initialEmbed n v)) := rfl

/-- A map fixing the final Pauli pair preserves the embedded preceding wires. -/
theorem initialEmbed_restrictionMap (f : WireSymplectic (K := K) (n + 1))
    (hz : f (lastVector zVector n) = lastVector zVector n)
    (hx : f (lastVector xVector n) = lastVector xVector n) (v : Wires K n) :
    initialEmbed n (f.restrictionMap v) = f (initialEmbed n v) := by
  have hlast : f (initialEmbed n v) (Fin.last n) = 0 := by
    rw [f.last_coordinates hz hx, initialEmbed_last]
  change Fin.snoc (Fin.init (f (initialEmbed n v))) 0 = _
  rw [← hlast, Fin.snoc_init_self]

/-- The restriction preserves the symplectic form. -/
theorem restrictionMap_preserves (f : WireSymplectic (K := K) (n + 1))
    (hz : f (lastVector zVector n) = lastVector zVector n)
    (hx : f (lastVector xVector n) = lastVector xVector n) (v w : Wires K n) :
    wiresBracket (f.restrictionMap v) (f.restrictionMap w) = wiresBracket v w := by
  rw [← wiresBracket_initialEmbed (f.restrictionMap v) (f.restrictionMap w),
    f.initialEmbed_restrictionMap hz hx, f.initialEmbed_restrictionMap hz hx,
    f.preserves, wiresBracket_initialEmbed]

/-- The induction restriction needed in Proposition 3.8. -/
def restrict (f : WireSymplectic (K := K) (n + 1))
    (hz : f (lastVector zVector n) = lastVector zVector n)
    (hx : f (lastVector xVector n) = lastVector xVector n) : WireSymplectic (K := K) n where
  toLinearEquiv := LinearEquiv.ofInjectiveEndo f.restrictionMap
    (wiresPreserver_injective f.restrictionMap (f.restrictionMap_preserves hz hx))
  preserves := f.restrictionMap_preserves hz hx

@[simp] theorem restrict_apply (f : WireSymplectic (K := K) (n + 1))
    (hz : f (lastVector zVector n) = lastVector zVector n)
    (hx : f (lastVector xVector n) = lastVector xVector n) (v : Wires K n) :
    f.restrict hz hx v = Fin.init (f (initialEmbed n v)) := rfl

/-- Act on the first n wires and leave the last wire idle. -/
def lift (f : WireSymplectic (K := K) n) : WireSymplectic (K := K) (n + 1) where
  toLinearEquiv := (splitLast n).trans
    ((f.toLinearEquiv.prodCongr (LinearEquiv.refl K (Vector K))).trans (splitLast n).symm)
  preserves v w := by
    change wiresBracket (Fin.snoc (f (Fin.init v)) (v (Fin.last n)))
      (Fin.snoc (f (Fin.init w)) (w (Fin.last n))) = _
    rw [wiresBracket_expand_last, wiresBracket_expand_last v w]
    simp [f.preserves]

@[simp] theorem lift_apply (f : WireSymplectic (K := K) n) (v : Wires K (n + 1)) :
    f.lift v = Fin.snoc (f (Fin.init v)) (v (Fin.last n)) := rfl

@[simp] theorem lift_initialEmbed (f : WireSymplectic (K := K) n) (v : Wires K n) :
    f.lift (initialEmbed n v) = initialEmbed n (f v) := by simp

@[simp] theorem lift_lastVector (f : WireSymplectic (K := K) n) (v : Vector K) :
    f.lift (lastVector v n) = lastVector v n := by
  rw [lift_apply, lastVector_eq_snoc]
  simp only [Fin.init_snoc, Fin.snoc_last]
  change (Fin.snoc (f.toLinearEquiv (0 : Wires K n)) v : Wires K (n + 1)) = _
  rw [map_zero]

/-- Fixing the final Pauli generators fixes every vector supported on that wire. -/
theorem fixes_lastVector (f : WireSymplectic (K := K) (n + 1))
    (hz : f (lastVector zVector n) = lastVector zVector n)
    (hx : f (lastVector xVector n) = lastVector xVector n) (v : Vector K) :
    f (lastVector v n) = lastVector v n := by
  have hv : lastVector v n = v.1 • lastVector zVector n + v.2 • lastVector xVector n := by
    calc
      _ = lastEmbed n v := (lastEmbed_apply v).symm
      _ = lastEmbed n (v.1 • zVector + v.2 • xVector) := by rw [← vector_decomposition]
      _ = _ := by rw [map_add, map_smul, map_smul, lastEmbed_apply, lastEmbed_apply]
  rw [hv, apply_add, apply_smul, apply_smul, hz, hx]

/-- The fixing map is exactly its restricted action tensored with an idle last wire. -/
theorem lift_restrict (f : WireSymplectic (K := K) (n + 1))
    (hz : f (lastVector zVector n) = lastVector zVector n)
    (hx : f (lastVector xVector n) = lastVector xVector n) :
    (f.restrict hz hx).lift = f := by
  apply WireSymplectic.ext
  intro v
  conv_rhs => rw [wire_decomposition v, apply_add, f.fixes_lastVector hz hx]
  rw [lift_apply, restrict_apply]
  have he := f.initialEmbed_restrictionMap hz hx (Fin.init v)
  change initialEmbed n (Fin.init (f (initialEmbed n (Fin.init v)))) = _ at he
  rw [← he, lastVector_eq_snoc]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end WireSymplectic

end QuditClifford.NormalBoxes
