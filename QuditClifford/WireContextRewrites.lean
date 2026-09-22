import QuditClifford.RelabelRewrites

/-!
# Interchange between embedded circuits and disjoint wire contexts

These structural derivations hold for complete expanded words, including
scalar letters and any number of idle wires. They support recursive use of
local box rules without assumptions about the semantic circuit action.
-/

noncomputable section
namespace QuditClifford.Circuit
variable {d l m n : ℕ} [NeZero d]
variable (g : (ZMod d)ˣ)

/-- A word avoiding the image of an embedding commutes with every circuit
embedded on those wires. -/
theorem classWord_commute_relabel_of_outside (ι : Fin m ↪ Fin n) (u : Word n) (v : Word m)
    (hu : ∀ a ∈ u, ∀ i, ι i ∉ a.support) :
    Commute (classWord g u) (classWord g (relabel ι v)) := by
  apply classWord_commute_of_disjoint
  intro a ha b hb
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
  rw [Gate.support_relabel]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hy
  exact hu a ha i hx

/-- The corresponding interchange is an actual contextual Figure 1 derivation. -/
theorem derives_commute_relabel_of_outside (ι : Fin m ↪ Fin n) (u : Word n) (v : Word m)
    (hu : ∀ a ∈ u, ∀ i, ι i ∉ a.support) :
    Derives g (u ++ relabel ι v) (relabel ι v ++ u) :=
  (classWord_eq_iff_derives g _ _).mp (classWord_commute_relabel_of_outside g ι u v hu).eq

/-- Disjoint embeddings allow arbitrary complete circuits to interchange. -/
theorem classWord_commute_relabels (ι : Fin l ↪ Fin n) (κ : Fin m ↪ Fin n)
    (hικ : ∀ i j, ι i ≠ κ j) (u : Word l) (v : Word m) :
    Commute (classWord g (relabel ι u)) (classWord g (relabel κ v)) := by
  apply classWord_commute_relabel_of_outside
  intro a ha j hj
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
  rw [Gate.support_relabel] at hj
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hj
  exact hικ i j hi

/-- Structural interchange between arbitrary circuits on disjoint named wires. -/
theorem derives_relabel_interchange (ι : Fin l ↪ Fin n) (κ : Fin m ↪ Fin n)
    (hικ : ∀ i j, ι i ≠ κ j) (u : Word l) (v : Word m) :
    Derives g (relabel ι u ++ relabel κ v) (relabel κ v ++ relabel ι u) :=
  (classWord_eq_iff_derives g _ _).mp (classWord_commute_relabels g ι κ hικ u v).eq

/-- A Fourier gate outside the embedded circuit's wire image commutes with it. -/
theorem classWord_H_commute_relabel (ι : Fin m ↪ Fin n) (i : Fin n)
    (hi : ∀ j, ι j ≠ i) (v : Word m) :
    Commute (classWord g [.H i]) (classWord g (relabel ι v)) := by
  apply classWord_commute_relabel_of_outside
  intro a ha j
  have he : a = .H i := by simpa using ha
  subst a
  simpa [Gate.support] using hi j

/-- A phase gate outside the embedded circuit's wire image commutes with it. -/
theorem classWord_S_commute_relabel (ι : Fin m ↪ Fin n) (i : Fin n)
    (hi : ∀ j, ι j ≠ i) (v : Word m) :
    Commute (classWord g [.S i]) (classWord g (relabel ι v)) := by
  apply classWord_commute_relabel_of_outside
  intro a ha j
  have he : a = .S i := by simpa using ha
  subst a
  simpa [Gate.support] using hi j

/-- The structural word interchange also holds after explicit Pauli erasure. -/
theorem symplecticClassWord_commute_relabel_of_outside
    (ι : Fin m ↪ Fin n) (u : Word n) (v : Word m)
    (hu : ∀ a ∈ u, ∀ i, ι i ∉ a.support) :
    Commute (symplecticClassWord g u) (symplecticClassWord g (relabel ι v)) :=
  congrArg (presentedToSymplectic g) (classWord_commute_relabel_of_outside g ι u v hu).eq

/-- Disjoint embeddings commute in the erased syntactic quotient as well. -/
theorem symplecticClassWord_commute_relabels (ι : Fin l ↪ Fin n) (κ : Fin m ↪ Fin n)
    (hικ : ∀ i j, ι i ≠ κ j) (u : Word l) (v : Word m) :
    Commute (symplecticClassWord g (relabel ι u)) (symplecticClassWord g (relabel κ v)) :=
  congrArg (presentedToSymplectic g) (classWord_commute_relabels g ι κ hικ u v).eq

end QuditClifford.Circuit
