import QuditClifford.CircuitRelabel
import QuditClifford.SymplecticRewrites

/-!
# Wire embeddings preserve actual rewrite derivations

Idle wires and injective renaming preserve each printed Figure 1 schema and
each explicit scalar/Pauli erasure. The contextual induction below allows
local box proofs to be used inside the recursive normal-form compiler.
-/
namespace QuditClifford.Presentation

/-- A letter map preserving generating relations preserves contextual rewriting. -/
theorem Derives.map {α β : Type*} {R : Word α → Word α → Prop}
    {S : Word β → Word β → Prop} (f : α → β)
    (hf : ∀ u v, R u v → Derives S (u.map f) (v.map f))
    {u v : Word α} (h : Derives R u v) : Derives S (u.map f) (v.map f) := by
  induction h with
  | refl w => exact .refl _
  | rule h => exact hf _ _ h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih => simpa only [List.map_append] using ih.context (l.map f) (r.map f)

end QuditClifford.Presentation

noncomputable section
namespace QuditClifford.Circuit
variable {d l m n : ℕ}

@[simp] theorem relabel_nil (ι : Fin m ↪ Fin n) : relabel ι [] = [] := rfl
@[simp] theorem relabel_cons (ι : Fin m ↪ Fin n) (a : Gate m) (w : Word m) :
    relabel ι (a :: w) = a.relabel ι :: relabel ι w := rfl
@[simp] theorem relabel_append (ι : Fin m ↪ Fin n) (u v : Word m) :
    relabel ι (u ++ v) = relabel ι u ++ relabel ι v := List.map_append

@[simp] theorem relabel_replicate (ι : Fin m ↪ Fin n) (k : ℕ) (a : Gate m) :
    relabel ι (List.replicate k a) = List.replicate k (a.relabel ι) := List.map_replicate

@[simp] theorem relabel_power (ι : Fin m ↪ Fin n) (w : Word m) (k : ℕ) :
    relabel ι (power w k) = power (relabel ι w) k := by
  simp [relabel, power, List.map_flatten]

@[simp] theorem relabel_scalar (ι : Fin m ↪ Fin n) (k : ℕ) :
    relabel ι (scalar k) = scalar k := by simp [scalar, Gate.relabel]

@[simp] theorem relabel_omegaPower (ι : Fin m ↪ Fin n) (a : ZMod d) :
    relabel ι (omegaPower a) = omegaPower a := by simp [omegaPower]

@[simp] theorem relabel_Sexp (ι : Fin m ↪ Fin n) (i : Fin m) (a : ZMod d) :
    relabel ι (Sexp i a) = Sexp (ι i) a := by simp [Sexp, Gate.relabel]

@[simp] theorem relabel_X (ι : Fin m ↪ Fin n) (i : Fin m) :
    relabel ι (X (d := d) i) = X (d := d) (ι i) := by simp [X, Gate.relabel]

@[simp] theorem relabel_Z (ι : Fin m ↪ Fin n) (i : Fin m) :
    relabel ι (Z (d := d) i) = Z (d := d) (ι i) := by simp [Z, Gate.relabel]

@[simp] theorem relabel_Xexp (ι : Fin m ↪ Fin n) (i : Fin m) (a : ZMod d) :
    relabel ι (Xexp i a) = Xexp (ι i) a := by simp [Xexp]

@[simp] theorem relabel_Zexp (ι : Fin m ↪ Fin n) (i : Fin m) (a : ZMod d) :
    relabel ι (Zexp i a) = Zexp (ι i) a := by simp [Zexp]

@[simp] theorem relabel_multiplier [NeZero d] (ι : Fin m ↪ Fin n) (i : Fin m) (a : (ZMod d)ˣ) :
    relabel ι (multiplier i a) = multiplier (ι i) a := by simp [multiplier, Gate.relabel]

@[simp] theorem relabel_CX (ι : Fin m ↪ Fin n) (i j : Fin m) (hij : i ≠ j) :
    relabel ι (CX i j hij) = CX (ι i) (ι j) (fun h => hij (ι.injective h)) := by
  simp [CX, Gate.relabel]

@[simp] theorem relabel_SWAP (ι : Fin m ↪ Fin n) (i j : Fin m) (hij : i ≠ j) :
    relabel ι (SWAP (d := d) i j hij) =
      SWAP (d := d) (ι i) (ι j) (fun h => hij (ι.injective h)) := by
  simp [SWAP, Gate.relabel]

@[simp] theorem relabel_CIZ (ι : Fin m ↪ Fin n) (i j k : Fin m)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    relabel ι (CIZ (d := d) i j k hij hjk hik) =
      CIZ (d := d) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)) := by
  simp [CIZ, Gate.relabel]

@[simp] theorem Gate.support_relabel (ι : Fin m ↪ Fin n) (a : Gate m) :
    (a.relabel ι).support = a.support.map ι := by
  cases a <;> simp [Gate.relabel, Gate.support]

/-- Wiring coherence survives every injection of the named wires. -/
theorem Structural.relabel (ι : Fin m ↪ Fin n) {u v : Word m} (h : Structural u v) :
    Structural (relabel ι u) (relabel ι v) := by
  cases h with
  | disjoint a b hab =>
      exact .disjoint (a.relabel ι) (b.relabel ι) (by
        simpa only [Gate.support_relabel, Finset.disjoint_map] using hab)
  | CZ_symmetry i j hij => exact .CZ_symmetry (ι i) (ι j) (fun h => hij (ι.injective h))

variable [NeZero d] (g : (ZMod d)ˣ)

set_option maxHeartbeats 800000 in
/-- Every one of the sixteen fully expanded schemas is natural in the wire injection. -/
theorem Figure1Rule.relabel (ι : Fin m ↪ Fin n) {u v : Word m} (h : Figure1Rule g u v) :
    Figure1Rule g (relabel ι u) (relabel ι v) := by
  cases h with
  | C0 => simpa using (Figure1Rule.C0 (n := n) (g := g))
  | C1 i => simpa [Gate.relabel] using (Figure1Rule.C1 (g := g) (ι i))
  | C2 i => simpa [Gate.relabel] using (Figure1Rule.C2 (g := g) (ι i))
  | C3 i k => simpa using (Figure1Rule.C3 (g := g) (ι i) k)
  | C4 i => simpa [Gate.relabel] using (Figure1Rule.C4 (g := g) (ι i))
  | C5 i => simpa [Gate.relabel] using (Figure1Rule.C5 (g := g) (ι i))
  | C6 i j hij => simpa [Gate.relabel] using
      (Figure1Rule.C6 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C7 i j hij => simpa using
      (Figure1Rule.C7 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C8 i j hij => simpa [Gate.relabel] using
      (Figure1Rule.C8 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C9 i j hij => simpa [Gate.relabel] using
      (Figure1Rule.C9 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C10 i j hij => simpa [Gate.relabel] using
      (Figure1Rule.C10 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C11 i j hij => simpa [Gate.relabel] using
      (Figure1Rule.C11 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C12 i j hij => simpa [Gate.relabel] using
      (Figure1Rule.C12 (g := g) (ι i) (ι j) (fun h => hij (ι.injective h)))
  | C13 i j k hij hjk hik => simpa using
      (Figure1Rule.C13 (g := g) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)))
  | C14 i j k hij hjk hik => simpa [Gate.relabel] using
      (Figure1Rule.C14 (g := g) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)))
  | C15 i j k hij hjk hik => simpa [Gate.relabel] using
      (Figure1Rule.C15 (g := g) (ι i) (ι j) (ι k)
        (fun h => hij (ι.injective h)) (fun h => hjk (ι.injective h))
        (fun h => hik (ι.injective h)))

theorem Rules.relabel (ι : Fin m ↪ Fin n) {u v : Word m} (h : Rules g u v) :
    Rules g (relabel ι u) (relabel ι v) :=
  h.elim (fun h => Or.inl (h.relabel ι)) (fun h => Or.inr (h.relabel g ι))

/-- Actual exact derivations can be embedded in a larger register. -/
theorem derives_relabel (ι : Fin m ↪ Fin n) {u v : Word m} (h : Derives g u v) :
    Derives g (relabel ι u) (relabel ι v) :=
  h.map (Gate.relabel ι) (fun _ _ hr => .rule (hr.relabel g ι))

theorem ProjectiveRules.relabel (ι : Fin m ↪ Fin n) {u v : Word m}
    (h : ProjectiveRules g u v) : ProjectiveRules g (relabel ι u) (relabel ι v) := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact Or.inl (h.relabel g ι)
  · exact Or.inr ⟨rfl, rfl⟩

theorem SymplecticRules.relabel (ι : Fin m ↪ Fin n) {u v : Word m}
    (h : SymplecticRules g u v) : SymplecticRules g (relabel ι u) (relabel ι v) := by
  rcases h with h | ⟨i, (rfl | rfl), rfl⟩
  · exact Or.inl (h.relabel g ι)
  · exact Or.inr ⟨ι i, Or.inl (relabel_X ι i), rfl⟩
  · exact Or.inr ⟨ι i, Or.inr (relabel_Z ι i), rfl⟩

/-- Scalar-erased derivations also transport to arbitrary named wires. -/
theorem projectiveDerives_relabel (ι : Fin m ↪ Fin n) {u v : Word m}
    (h : ProjectiveDerives g u v) : ProjectiveDerives g (relabel ι u) (relabel ι v) :=
  h.map (Gate.relabel ι) (fun _ _ hr => .rule (hr.relabel g ι))

/-- Scalar-and-Pauli-erased derivations transport to arbitrary named wires. -/
theorem symplecticDerives_relabel (ι : Fin m ↪ Fin n) {u v : Word m}
    (h : SymplecticDerives g u v) : SymplecticDerives g (relabel ι u) (relabel ι v) :=
  h.map (Gate.relabel ι) (fun _ _ hr => .rule (hr.relabel g ι))

/-- Disjoint primitive supports give commutation of entire word classes. -/
theorem classWord_commute_of_disjoint (u v : Word n)
    (huv : ∀ a ∈ u, ∀ b ∈ v, Disjoint a.support b.support) :
    Commute (classWord g u) (classWord g v) := by
  have hw (a : Gate n) (ha : ∀ b ∈ v, Disjoint a.support b.support) :
      Commute (classWord g [a]) (classWord g v) := by
    clear huv
    induction v with
    | nil => exact Commute.one_right _
    | cons b v ih =>
      have hb : Commute (classWord g [a]) (classWord g [b]) :=
        (classWord_eq_iff_derives g _ _).mpr (.rule (Or.inl (.disjoint a b (ha b (by simp)))))
      exact hb.mul_right (ih (fun b hb => ha b (by simp [hb])))
  induction u with
  | nil => exact Commute.one_left _
  | cons a u ih =>
      exact (hw a (huv a (by simp))).mul_left (ih (fun b hb => huv b (by simp [hb])))

/-- Placement of a one-wire circuit at any named wire. -/
def singleWireEmbedding (i : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Every embedded one-wire word commutes with a word avoiding that wire. -/
theorem classWord_commute_singleWire (i : Fin n) (u : Word n) (v : Word 1)
    (hu : ∀ a ∈ u, i ∉ a.support) :
    Commute (classWord g u) (classWord g (relabel (singleWireEmbedding i) v)) := by
  apply classWord_commute_of_disjoint
  intro a ha b hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
  cases c with
  | scalar => simp [Gate.relabel, Gate.support]
  | H j => simpa [Gate.relabel, Gate.support, singleWireEmbedding] using hu a ha
  | S j => simpa [Gate.relabel, Gate.support, singleWireEmbedding] using hu a ha
  | CZ j k hjk => exact (hjk (Subsingleton.elim _ _)).elim

/-- In particular, an expanded multiplier commutes with words off its wire. -/
theorem classWord_commute_multiplier_of_avoids (i : Fin n) (a : (ZMod d)ˣ) (u : Word n)
    (hu : ∀ b ∈ u, i ∉ b.support) :
    Commute (classWord g u) (classWord g (multiplier i a)) := by
  simpa only [relabel_multiplier, singleWireEmbedding, Function.Embedding.coeFn_mk] using
    classWord_commute_singleWire g i u (multiplier (0 : Fin 1) a) hu

end QuditClifford.Circuit

namespace QuditClifford.NormalBoxes
open Circuit
variable {d m n : ℕ} [Fact d.Prime]

@[simp] theorem ABox.relabel_toWord (ι : Fin m ↪ Fin n)
    (A : ABox (ZMod d)) (i : Fin m) :
    relabel ι (A.toWord i) = A.toWord (ι i) := by
  by_cases ha : A.a = 0 <;> simp [ABox.toWord, ha, Gate.relabel]

@[simp] theorem relabel_eWord (ι : Fin m ↪ Fin n) (b : ZMod d) (i : Fin m) :
    relabel ι (eWord b i) = eWord b (ι i) := by simp [eWord]

@[simp] theorem relabel_bWord (ι : Fin m ↪ Fin n) (a b : ZMod d)
    (i j : Fin m) (hij : i ≠ j) :
    relabel ι (bWord a b i j hij) =
      bWord a b (ι i) (ι j) (fun h => hij (ι.injective h)) := by
  by_cases ha : a = 0 <;> simp [bWord, ha, Gate.relabel]

@[simp] theorem relabel_dWord (ι : Fin m ↪ Fin n) (a b : ZMod d)
    (i j : Fin m) (hij : i ≠ j) :
    relabel ι (dWord a b i j hij) =
      dWord a b (ι i) (ι j) (fun h => hij (ι.injective h)) := by
  by_cases ha : a = 0 <;> simp [dWord, ha, Gate.relabel]

end QuditClifford.NormalBoxes
