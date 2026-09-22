import QuditClifford.ExactNormalForm
import QuditClifford.MultiplierSoundness

/-! # The remaining explicit rewrite-normalization obligation

A concrete normal primitive word is obtained from the proved unique exact
matrix normal form. Its interpretation and uniqueness are proved here.
Completeness is equivalent to deriving this normalization from Figure 1.
No constructor or theorem turns semantic equality into a rewrite derivation.
-/
noncomputable section
namespace QuditClifford.Circuit
variable {d n : ℕ} [NeZero d] [Fact d.Prime]

/-- Unique exact normal data of a primitive word's actual generated matrix. -/
def normalizeData (hd : Odd d) (w : Word n) : ExactNormalData d n :=
  (exactNormalEquiv hd).symm (generatedWord w)

/-- The compiled primitive word of the unique exact matrix normal form. -/
def normalizeWord (hd : Odd d) (w : Word n) : Word n := exactNormalWord (normalizeData hd w)

/-- The concrete normal word preserves the full complex matrix, including its sign. -/
theorem denote_normalizeWord (hd : Odd d) (w : Word n) :
    denote d (normalizeWord hd w) = denote d w := by
  have h := (exactNormalEquiv (n := n) hd).apply_symm_apply (generatedWord w)
  change exactNormalMatrix hd (normalizeData hd w) = generatedWord w at h
  rw [← generatedWord_exactNormalWord] at h
  exact congrArg (fun U : generatedCliffordGroup d n => U.val.val) h

/-- Normal data is a complete invariant of exact circuit matrices. -/
theorem normalizeData_eq_iff_denote_eq (hd : Odd d) (u v : Word n) :
    normalizeData hd u = normalizeData hd v ↔ denote d u = denote d v := by
  change (exactNormalEquiv hd).symm (generatedWord u) =
    (exactNormalEquiv hd).symm (generatedWord v) ↔ _
  rw [(exactNormalEquiv hd).symm.injective.eq_iff]
  exact ⟨fun h => congrArg (fun U : generatedCliffordGroup d n => U.val.val) h,
    fun h => Subtype.ext (Subtype.ext h)⟩

theorem normalizeWord_eq_of_denote_eq (hd : Odd d) {u v : Word n}
    (h : denote d u = denote d v) : normalizeWord hd u = normalizeWord hd v :=
  congrArg exactNormalWord ((normalizeData_eq_iff_denote_eq hd u v).mpr h)

/-- Canonical normalization is idempotent at the actual normal-word level. -/
theorem normalizeWord_idempotent (hd : Odd d) (w : Word n) :
    normalizeWord hd (normalizeWord hd w) = normalizeWord hd w :=
  normalizeWord_eq_of_denote_eq hd (denote_normalizeWord hd w)

/-- The exact outstanding constructive obligation for Theorem 4.10: each word
must be related to this concrete normal word by the displayed rewrite rules. -/
def DerivablyNormalizes (hd : Odd d) (g : (ZMod d)ˣ) : Prop :=
  ∀ w : Word n, Derives g w (normalizeWord hd w)

/-- The unique actual normal form discharges semantic uniqueness; only explicit
Figure 1 normalization derivations are required for the converse implication. -/
theorem figure1Complete_iff_derivablyNormalizes (hd : Odd d) (g : (ZMod d)ˣ) :
    Figure1Complete (n := n) g ↔ DerivablyNormalizes (n := n) hd g := by
  constructor
  · intro hc w
    exact hc w (normalizeWord hd w) (denote_normalizeWord hd w).symm
  · intro hn u v huv
    exact (hn u).trans ((normalizeWord_eq_of_denote_eq hd huv) ▸ (hn v).symm)

end QuditClifford.Circuit
