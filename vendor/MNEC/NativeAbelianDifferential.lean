module

public import Jacobians.Forms.NativeCanonical

@[expose] public section

open scoped Manifold ContDiff Topology Classical

noncomputable section

namespace MNEC.NativeAbelianDifferential

open Set Filter

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- An arbitrary nonzero analytic cotangent section on a compact connected
complex curve. This type carries no splitting, dynamical or classification
certificate. -/
abbrev Differential := {α : Jacobians.HolomorphicOneForms X // α ≠ 0}

variable {X}

def zeroSet (q : Differential X) : Set X := {x | q.val.toFun x = 0}

def regularSet (q : Differential X) : Set X := (zeroSet q)ᶜ

def divisor (q : Differential X) : X →₀ ℤ :=
  Jacobians.NativeCanonical.canonicalDivisorOf q.val q.property

def degree (q : Differential X) : ℤ := (divisor q).sum (fun _ n => n)

theorem toFun_eq_zero_iff_localRep_self (q : Differential X) (x : X) :
    q.val.toFun x = 0 ↔ Jacobians.Montel.localRep q.val x x = 0 := by
  constructor
  · exact Jacobians.NativeCanonical.localRep_eq_zero_of_toFun_eq_zero q.val x
  · exact Jacobians.NativeCanonical.toFun_eq_zero_of_localRep_eq_zero q.val
      (mem_chart_source ℂ x)

theorem zeroSet_finite (q : Differential X) : (zeroSet q).Finite := by
  have heq : zeroSet q = {x | Jacobians.Montel.localRep q.val x x = 0} := by
    ext x
    exact toFun_eq_zero_iff_localRep_self q x
  rw [heq]
  exact Jacobians.NativeCanonical.finite_localRep_self_eq_zero q.val q.property

theorem zeroSet_closed (q : Differential X) : IsClosed (zeroSet q) :=
  (zeroSet_finite q).isClosed

theorem regularSet_open (q : Differential X) : IsOpen (regularSet q) :=
  (zeroSet_closed q).isOpen_compl

theorem regularSet_nonempty (q : Differential X) : (regularSet q).Nonempty := by
  by_contra h
  apply q.property
  refine ContMDiffSection.ext fun x => ?_
  have hx : x ∈ zeroSet q := by
    by_contra hx
    exact h ⟨x, hx⟩
  exact hx

theorem order_eq_zero_iff_regular (q : Differential X) (x : X) :
    Jacobians.NativeCanonical.omegaOrderAt q.val x = 0 ↔ x ∈ regularSet q := by
  constructor
  · intro ho hx
    have han := Jacobians.NativeCanonical.analyticAt_coeffAt_self q.val x
    obtain ⟨c, hc, hlim⟩ :=
      tendsto_ne_zero_of_meromorphicOrderAt_eq_zero han.meromorphicAt ho
    have hvalue : c = Jacobians.NativeCanonical.coeffAt q.val x ((chartAt ℂ x) x) :=
      tendsto_nhds_unique hlim (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    apply hc
    rw [hvalue, Jacobians.NativeCanonical.coeffAt_self_eq_localRep]
    exact (toFun_eq_zero_iff_localRep_self q x).mp hx
  · intro hx
    apply Jacobians.NativeCanonical.omegaOrderAt_eq_zero_of_localRep_ne_zero
    exact fun h => hx ((toFun_eq_zero_iff_localRep_self q x).mpr h)

/-- Actual native local order pattern of the principal genus-two stratum. -/
def HasTwoSimpleZeros (q : Differential X) : Prop :=
  ∃ p₀ p₁ : X, p₀ ≠ p₁ ∧ ∀ x : X,
    Jacobians.NativeCanonical.omegaOrderAt q.val x =
      if x = p₀ ∨ x = p₁ then 1 else 0

/-- Actual native local order pattern of the double-zero stratum. -/
def HasOneDoubleZero (q : Differential X) : Prop :=
  ∃ p : X, ∀ x : X, Jacobians.NativeCanonical.omegaOrderAt q.val x =
    if x = p then 2 else 0

def InH11 (q : Differential X) : Prop := genus X = 2 ∧ HasTwoSimpleZeros q

def InH2 (q : Differential X) : Prop := genus X = 2 ∧ HasOneDoubleZero q

theorem divisor_apply (q : Differential X) (x : X) :
    ((divisor q x : ℤ) : WithTop ℤ) = Jacobians.NativeCanonical.omegaOrderAt q.val x :=
  Jacobians.NativeCanonical.coe_canonicalDivisorOf q.val q.property x

theorem divisor_of_two_simple_zeros (q : Differential X) (p₀ p₁ : X) (hne : p₀ ≠ p₁)
    (h : ∀ x : X, Jacobians.NativeCanonical.omegaOrderAt q.val x =
      if x = p₀ ∨ x = p₁ then 1 else 0) :
    divisor q = Finsupp.single p₀ 1 + Finsupp.single p₁ 1 := by
  ext x
  apply WithTop.coe_injective
  rw [divisor_apply, h, Finsupp.add_apply]
  by_cases h₀ : x = p₀
  · subst x
    simp [hne]
  · by_cases h₁ : x = p₁
    · subst x
      simp [hne.symm]
    · simp [h₀, h₁]

theorem degree_of_two_simple_zeros (q : Differential X) (h : HasTwoSimpleZeros q) :
    degree q = 2 := by
  obtain ⟨p₀, p₁, hne, h⟩ := h
  unfold degree
  rw [divisor_of_two_simple_zeros q p₀ p₁ hne h, Finsupp.sum_add_index']
  · simp
  · intro a
    rfl
  · intro a b c
    rfl

theorem divisor_of_one_double_zero (q : Differential X) (p : X)
    (h : ∀ x : X, Jacobians.NativeCanonical.omegaOrderAt q.val x =
      if x = p then 2 else 0) : divisor q = Finsupp.single p 2 := by
  ext x
  apply WithTop.coe_injective
  rw [divisor_apply, h]
  by_cases hx : x = p <;> simp [hx]

theorem degree_of_one_double_zero (q : Differential X) (h : HasOneDoubleZero q) :
    degree q = 2 := by
  obtain ⟨p, h⟩ := h
  unfold degree
  rw [divisor_of_one_double_zero q p h]
  simp

end MNEC.NativeAbelianDifferential

