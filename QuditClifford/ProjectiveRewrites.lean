import QuditClifford.DerivedPauliRewrites
import QuditClifford.CyclotomicScalars
import QuditClifford.ScalarCompleteness

/-! # Explicit scalar erasure and exact lifting of circuit rewrites

Projective rewriting adds only the equation deleting a primitive scalar to
the actual Figure 1 relations. An induction on such a derivation lifts it to
an exact derivation with a scalar correction. Consequently projective rewrite
completeness implies exact rewrite completeness, using the already proved C0
scalar completeness. Neither completeness statement is assumed as a theorem.
-/
noncomputable section
namespace QuditClifford.Circuit
open Matrix
variable {d n : ℕ} [NeZero d]

/-- The precise scalar-erased relation: the actual Figure 1 rules, plus deletion
of one primitive scalar. It contains no semantic-equality constructor. -/
def ProjectiveRules (g : (ZMod d)ˣ) (u v : Word n) : Prop :=
  Rules g u v ∨ (u = [.scalar] ∧ v = [])

/-- Contextual rewriting after forgetting only global scalar gates. -/
def ProjectiveDerives (g : (ZMod d)ˣ) : Word n → Word n → Prop :=
  Presentation.Derives (ProjectiveRules g)

theorem derives_projective (g : (ZMod d)ˣ) {u v : Word n} (h : Derives g u v) :
    ProjectiveDerives g u v :=
  h.mono (fun _ _ hr => .rule (Or.inl hr))

theorem projectiveDerives_scalar (g : (ZMod d)ˣ) (k : ℕ) :
    ProjectiveDerives (n := n) g (scalar k) [] := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    have hs : ProjectiveDerives (n := n) g [.scalar] [] := .rule (Or.inr ⟨rfl, rfl⟩)
    exact hs.append ih

variable [Fact d.Prime]
variable (g : (ZMod d)ˣ) [Fact (Odd d)] [Fact (orderOf g = d-1)]

private abbrev scalarClass : PresentedCircuit g n := classWord g [.scalar]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem scalarClass_commute (q : PresentedCircuit g n) :
    Commute (scalarClass g) q := by
  obtain ⟨w, rfl⟩ := classWord_surjective g q
  exact (classWord_eq_iff_derives g _ _).mpr (derives_scalar_one_commute g w)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
private theorem scalarClass_finiteOrder : IsOfFinOrder (scalarClass (n := n) g) := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨2*d, Nat.mul_pos (by decide) (NeZero.pos d), ?_⟩
  have he := (classWord_eq_iff_derives g (scalar (n := n) (2*d)) []).mpr
    (.rule (Or.inr Figure1Rule.C0))
  simpa only [scalar, classWord_replicate, classWord_nil] using he

/-- Every erased derivation has an explicit central scalar correction in the
genuine exact syntactic group. -/
private theorem projectiveDerives_lift_zpow {u v : Word n}
    (h : ProjectiveDerives g u v) :
    ∃ k : ℤ, classWord g u = scalarClass g ^ k * classWord g v := by
  induction h with
  | refl w => exact ⟨0, by simp⟩
  | @rule u v hr =>
    rcases hr with hr | ⟨rfl, rfl⟩
    · exact ⟨0, by simpa using (classWord_eq_iff_derives g u v).mpr (.rule hr)⟩
    · exact ⟨1, by simp [scalarClass]⟩
  | symm h ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨-k, ?_⟩
    rw [hk, _root_.zpow_neg]
    group
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨k, hk⟩ := ih₁
    obtain ⟨l, hl⟩ := ih₂
    exact ⟨k+l, by rw [hk, hl, _root_.zpow_add, mul_assoc]⟩
  | context l r h ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k, ?_⟩
    simp only [classWord_append, hk]
    rw [← mul_assoc (classWord g l),
      ((scalarClass_commute g (classWord g l)).zpow_left k).eq.symm]
    simp only [mul_assoc]

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Scalar erasure lifts back to the original exact rules with a natural-power
scalar correction. This is proved for all derivations, not a lifting hypothesis. -/
theorem projectiveDerives_lift (hd : Odd d) (hg : orderOf g = d-1)
    {u v : Word n} (h : ProjectiveDerives g u v) :
    ∃ k : ℕ, Derives g u (scalar k ++ v) := by
  letI : Fact (Odd d) := ⟨hd⟩
  letI : Fact (orderOf g = d-1) := ⟨hg⟩
  obtain ⟨k, hk⟩ := projectiveDerives_lift_zpow g h
  have hm : scalarClass (n := n) g ^ k ∈ Subgroup.zpowers (scalarClass g) :=
    Subgroup.zpow_mem_zpowers _ _
  obtain ⟨l, hl⟩ := (scalarClass_finiteOrder g).mem_powers_iff_mem_zpowers.mpr hm
  refine ⟨l, (classWord_eq_iff_derives g _ _).mp ?_⟩
  rw [classWord_append, scalar, classWord_replicate]
  change classWord g u = scalarClass g ^ l * classWord g v
  change scalarClass g ^ l = scalarClass g ^ k at hl
  exact hl ▸ hk

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- The projective congruence is exactly exact derivability with a scalar prefix. -/
theorem projectiveDerives_iff_scalar_derives (hd : Odd d) (hg : orderOf g = d-1)
    (u v : Word n) :
    ProjectiveDerives g u v ↔ ∃ k : ℕ, Derives g u (scalar k ++ v) := by
  constructor
  · exact projectiveDerives_lift g hd hg
  · rintro ⟨k, hk⟩
    exact (derives_projective g hk).trans ((projectiveDerives_scalar g k).append_right v)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- An erased derivation between exactly equal matrices is already an exact
Figure 1 derivation. The residual scalar is removed by the proved C0 fragment. -/
theorem derives_of_projectiveDerives_of_denote_eq (hd : Odd d) (hg : orderOf g = d-1)
    {u v : Word n} (hp : ProjectiveDerives g u v) (he : denote d u = denote d v) :
    Derives g u v := by
  obtain ⟨k, hk⟩ := projectiveDerives_lift g hd hg hp
  have hs : denote d (scalar (n := n) k) = 1 := by
    have hh := (figure1_sound hd g u (scalar k ++ v) hk).symm.trans he
    rw [denote_append] at hh
    have hr := congrArg (fun A : QuditOperator d n => A * (denote d v)ᴴ) hh
    have hv : denote d v * (denote d v)ᴴ = 1 := (denote_unitary v).2
    simpa only [mul_assoc, hv, mul_one] using hr
  have hzero : Derives (n := n) g (scalar k) [] := scalar_complete hd g k 0 hs
  exact hk.trans (hzero.append_right v)

/-- The remaining projective completeness target uses the explicit scalar-erased
rules above, rather than identifying circuits by their matrix action. -/
def Figure1ProjectiveComplete (g : (ZMod d)ˣ) : Prop :=
  ∀ u v : Word n, ProjectiveEq (denote d u) (denote d v) → ProjectiveDerives g u v

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- The explicit scalar-erased presentation is sound for actual projective
matrix equality, independently of any completeness claim. -/
theorem projectiveDerives_sound (hd : Odd d) {u v : Word n}
    (h : ProjectiveDerives g u v) : ProjectiveEq (denote d u) (denote d v) := by
  induction h with
  | refl w => exact ProjectiveEq.refl _
  | @rule u v hr =>
    rcases hr with hr | ⟨rfl, rfl⟩
    · exact ProjectiveEq.of_eq (figure1_sound hd g u v (.rule hr))
    · refine ⟨scalarGenerator d,
        (scalarGenerator_primitive d hd).ne_zero (Nat.mul_ne_zero (by decide) (NeZero.ne d)), ?_⟩
      simp [denote, Presentation.eval, Gate.denote]
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | context l r h ih =>
    simpa only [denote_append] using
      ((ProjectiveEq.refl (denote d l)).mul ih).mul (ProjectiveEq.refl (denote d r))

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- The final scalar-extension step is fully instantiated. Only completeness
of the explicitly scalar-erased presentation remains an input. -/
theorem figure1Complete_of_projectiveComplete (hd : Odd d) (hg : orderOf g = d-1)
    (hp : Figure1ProjectiveComplete (n := n) g) : Figure1Complete (n := n) g := by
  intro u v he
  exact derives_of_projectiveDerives_of_denote_eq g hd hg
    (hp u v (ProjectiveEq.of_eq he)) he

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- Exact completeness conversely implies the explicit projective completeness:
the cyclotomic scalar theorem realizes the phase between two circuit matrices. -/
theorem projectiveComplete_of_figure1Complete (hd : Odd d)
    (hc : Figure1Complete (n := n) g) : Figure1ProjectiveComplete (n := n) g := by
  rintro u v ⟨c, _, huv⟩
  have hscalar : denote d (u ++ inverseWord d v) = c • (1 : QuditOperator d n) := by
    rw [denote_append, denote_inverseWord hd, huv, Matrix.smul_mul]
    have hv : denote d v * (denote d v)ᴴ = 1 := (denote_unitary v).2
    rw [hv]
  obtain ⟨k, hk⟩ := scalar_eq_scalarGenerator_pow hd (u ++ inverseWord d v) c hscalar
  have hder : Derives g u (scalar k ++ v) := by
    apply hc
    rw [denote_append, denote_scalar, Matrix.smul_mul, one_mul, ← hk]
    exact huv
  exact (derives_projective g hder).trans ((projectiveDerives_scalar g k).append_right v)

omit [Fact (Odd d)] [Fact (orderOf g = d-1)] in
/-- For the selected actual relations, the exact and scalar-erased completeness
targets are equivalent. This proves the scalar lifting step, not either target. -/
theorem figure1Complete_iff_projectiveComplete (hd : Odd d) (hg : orderOf g = d-1) :
    Figure1Complete (n := n) g ↔ Figure1ProjectiveComplete (n := n) g :=
  ⟨projectiveComplete_of_figure1Complete g hd,
    figure1Complete_of_projectiveComplete g hd hg⟩

end QuditClifford.Circuit
