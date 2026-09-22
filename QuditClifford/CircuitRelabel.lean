import QuditClifford.CircuitSymplectic

/-! # Primitive wire injections and exponent semantics in wirewise coordinates -/
noncomputable section
namespace QuditClifford.Circuit
open NormalBoxes
variable {d m n : ℕ}

/-- Injectively rename the wires of one primitive gate. -/
def Gate.relabel (ι : Fin m ↪ Fin n) : Gate m → Gate n
  | .scalar => .scalar
  | .H i => .H (ι i)
  | .S i => .S (ι i)
  | .CZ i j h => .CZ (ι i) (ι j) (fun e => h (ι.injective e))

/-- Injective wire renaming keeps the primitive word and all exact scalar letters. -/
def relabel (ι : Fin m ↪ Fin n) (w : Word m) : Word n := w.map (Gate.relabel ι)

/-- Primitive exponent action expressed as one `(z,x)` pair per wire. -/
def Gate.wireAction (d : ℕ) (g : Gate n) (v : Wires (ZMod d) n) : Wires (ZMod d) n :=
  (wiresCoordinates d n).symm (g.symplecticAction d (wiresCoordinates d n v))

/-- Word exponent action in wirewise coordinates. -/
def wireAction (d : ℕ) (w : Word n) (v : Wires (ZMod d) n) : Wires (ZMod d) n :=
  (wiresCoordinates d n).symm (symplecticAction d w (wiresCoordinates d n v))

@[simp] theorem wireAction_nil (v : Wires (ZMod d) n) : wireAction d [] v = v := rfl

@[simp] theorem wireAction_cons (g : Gate n) (w : Word n) (v : Wires (ZMod d) n) :
    wireAction d (g :: w) v = g.wireAction d (wireAction d w v) := rfl

@[simp] theorem wireAction_append (w t : Word n) (v : Wires (ZMod d) n) :
    wireAction d (w ++ t) v = wireAction d w (wireAction d t v) := by
  simp [wireAction, symplecticAction_append]

@[simp] theorem Gate.wireAction_scalar (v : Wires (ZMod d) n) :
    Gate.wireAction d .scalar v = v := rfl

@[simp] theorem Gate.wireAction_H (i k : Fin n) (v : Wires (ZMod d) n) :
    Gate.wireAction d (.H i) v k = if k = i then ((v k).2, -(v k).1) else v k := by
  by_cases h : k = i <;>
    simp [Gate.wireAction, Gate.symplecticAction, wiresCoordinates, localHadamard, h]

@[simp] theorem Gate.wireAction_S (i k : Fin n) (v : Wires (ZMod d) n) :
    Gate.wireAction d (.S i) v k = if k = i then ((v k).1 + (v k).2, (v k).2) else v k := by
  by_cases h : k = i <;>
    simp [Gate.wireAction, Gate.symplecticAction, wiresCoordinates, localPhaseShear, h]

@[simp] theorem Gate.wireAction_CZ (i j k : Fin n) (hij : i ≠ j) (v : Wires (ZMod d) n) :
    Gate.wireAction d (.CZ i j hij) v k =
      ((v k).1 + (if k = i then (v j).2 else 0) + (if k = j then (v i).2 else 0), (v k).2) := by
  simp [Gate.wireAction, Gate.symplecticAction, wiresCoordinates, controlledPhase, exponentBasis,
    mul_ite]

/-- On injected wires, a renamed primitive acts on the restricted input. -/
theorem Gate.wireAction_relabel_at (ι : Fin m ↪ Fin n) (g : Gate m)
    (v : Wires (ZMod d) n) (k : Fin m) :
    (g.relabel ι).wireAction d v (ι k) = g.wireAction d (v ∘ ι) k := by
  cases g <;> simp [Gate.relabel, ι.injective.eq_iff, Function.comp_apply]

/-- A renamed primitive leaves every wire outside the injection unchanged. -/
theorem Gate.wireAction_relabel_outside (ι : Fin m ↪ Fin n) (g : Gate m)
    (v : Wires (ZMod d) n) (k : Fin n) (hk : ∀ i, k ≠ ι i) :
    (g.relabel ι).wireAction d v k = v k := by
  cases g <;> simp [Gate.relabel, hk]

/-- Restriction commutes with executing an injectively renamed word. -/
theorem wireAction_relabel_restrict (ι : Fin m ↪ Fin n) (w : Word m)
    (v : Wires (ZMod d) n) :
    wireAction d (relabel ι w) v ∘ ι = wireAction d w (v ∘ ι) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    funext k
    change (g.relabel ι).wireAction d (wireAction d (relabel ι w) v) (ι k) = _
    rw [Gate.wireAction_relabel_at, ih]
    rfl

/-- Renaming a word does not act on wires outside the injection. -/
theorem wireAction_relabel_outside (ι : Fin m ↪ Fin n) (w : Word m)
    (v : Wires (ZMod d) n) (k : Fin n) (hk : ∀ i, k ≠ ι i) :
    wireAction d (relabel ι w) v k = v k := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    change (g.relabel ι).wireAction d (wireAction d (relabel ι w) v) k = _
    rw [Gate.wireAction_relabel_outside ι g _ k hk, ih]

/-- Skip the first wire. -/
def shiftEmbedding (n : ℕ) : Fin n ↪ Fin (n + 1) := ⟨Fin.succ, Fin.succ_injective n⟩

/-- Leave a final wire idle. -/
def initialEmbedding (n : ℕ) : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective _⟩

@[simp] theorem wireAction_relabel_shift (w : Word n) (v : Wires (ZMod d) (n + 1)) :
    wireAction d (relabel (shiftEmbedding n) w) v = Fin.cons (v 0) (wireAction d w (Fin.tail v)) := by
  apply ZNormal.wires_ext
  · exact wireAction_relabel_outside _ w v 0 (fun i => (Fin.succ_ne_zero i).symm)
  · exact wireAction_relabel_restrict _ w v

@[simp] theorem wireAction_relabel_initial (w : Word n) (v : Wires (ZMod d) (n + 1)) :
    wireAction d (relabel (initialEmbedding n) w) v =
      Fin.snoc (wireAction d w (Fin.init v)) (v (Fin.last n)) := by
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simpa using wireAction_relabel_outside (initialEmbedding n) w v (Fin.last n)
      (fun i => (Fin.castSucc_ne_last i).symm)
  · have h := congrFun (wireAction_relabel_restrict (initialEmbedding n) w v) i
    simpa [initialEmbedding, Function.comp_apply, Fin.init] using h

variable [NeZero d]

@[simp] theorem wireAction_Sexp (i k : Fin n) (a : ZMod d) (v : Wires (ZMod d) n) :
    wireAction d (Sexp i a) v k =
      if k = i then ((v k).1 + a * (v k).2, (v k).2) else v k := by
  by_cases h : k = i <;>
    simp [wireAction, symplecticAction_Sexp, wiresCoordinates, localPhaseShear, h]

@[simp] theorem wireAction_multiplier [Fact d.Prime] (i k : Fin n) (a : (ZMod d)ˣ)
    (v : Wires (ZMod d) n) :
    wireAction d (multiplier i a) v k =
      if k = i then ((↑a⁻¹ : ZMod d) * (v k).1, (↑a : ZMod d) * (v k).2) else v k := by
  unfold wireAction
  rw [symplecticAction_multiplier]
  by_cases h : k = i <;>
    simp only [wiresCoordinates, LinearEquiv.coe_symm_mk, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk, localMultiplier, h, ite_true, ite_false, Pi.smul_apply, smul_eq_mul]

@[simp] theorem wireAction_power_CX (i j k : Fin n) (hij : i ≠ j) (a : ZMod d)
    (v : Wires (ZMod d) n) :
    wireAction d (power (CX i j hij) a.val) v k =
      ((v k).1 - (if k = i then a * (v j).1 else 0),
        (v k).2 + (if k = j then a * (v i).2 else 0)) := by
  simp [wireAction, symplecticAction_power_CX, wiresCoordinates, controlledAdd, exponentBasis,
    mul_ite]

@[simp] theorem wireAction_replicate_CZ (i j k : Fin n) (hij : i ≠ j) (a : ZMod d)
    (v : Wires (ZMod d) n) :
    wireAction d (List.replicate a.val (.CZ i j hij)) v k =
      ((v k).1 + (if k = i then a * (v j).2 else 0) +
        (if k = j then a * (v i).2 else 0), (v k).2) := by
  simp [wireAction, symplecticAction_replicate_CZ, wiresCoordinates, controlledPhase, exponentBasis,
    mul_ite]

omit [NeZero d] in
@[simp] theorem wireAction_SWAP (i j k : Fin n) (hij : i ≠ j) (v : Wires (ZMod d) n) :
    wireAction d (SWAP (d := d) i j hij) v k = v (Equiv.swap i j k) := by
  simp [wireAction, symplecticAction_SWAP, wiresCoordinates, swapAction]

end QuditClifford.Circuit
