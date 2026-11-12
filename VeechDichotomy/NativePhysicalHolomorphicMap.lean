module

public import VeechDichotomy.NativePhysicalDifferentialEquiv
public import VeechDichotomy.HolomorphicCurveMaps
public import Mathlib.Topology.Perfect

/-! A continuous whole-curve map with an actual identity physical
derivative on the regular locus is holomorphic and pulls back the target
form to the source form. This also applies to maps with ramification. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativePhysicalHolomorphicMap

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativePrimitiveTransitions Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {q : Differential X} {r : Differential Y}

theorem nontrivial (q : Differential X) : Nontrivial X := by
  by_contra hn
  have : Subsingleton X := not_nontrivial_iff_subsingleton.mp hn
  obtain ⟨x, hx⟩ := regularSet_nonempty q
  let P := chosen q ⟨x, hx⟩
  have hfun : (P.chart : X → ℂ) = fun _ => P.chart x :=
    funext fun y => congrArg P.chart (Subsingleton.elim y x)
  have hd := (P.derivative x P.center).mfderiv
  rw [hfun, mfderiv_const] at hd
  exact hx hd.symm

theorem regularSet_dense (q : Differential X) : Dense (regularSet q) := by
  let : Nontrivial X := nontrivial q
  have h := (dense_univ : Dense (univ : Set X)).sdiff_finite (zeroSet_finite q)
  have heq : (univ : Set X) \ zeroSet q = regularSet q := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨mem_univ _, hx⟩⟩
  rwa [heq] at h

theorem form_eq_of_eqOn_regular (q : Differential X) (α β : Jacobians.HolomorphicOneForms X)
    (heq : ∀ x ∈ regularSet q, α.toFun x = β.toFun x) : α = β := by
  by_contra hn
  let δ : Differential X := ⟨α - β, sub_ne_zero.mpr hn⟩
  obtain ⟨x, hxδ, hxq⟩ := (regularSet_dense q).inter_open_nonempty
    (regularSet δ) (regularSet_open δ) (regularSet_nonempty δ)
  apply hxδ
  change α.toFun x - β.toFun x = 0
  rw [heq x hxq, sub_self]

local instance : ChartedSpace Plane (Regular q) := chartedSpace q
local instance : ChartedSpace Plane (Regular r) := chartedSpace r

theorem holomorphic (F : X → Y) (hc : Continuous F) (R : Regular q → Regular r)
    (hR : Continuous R) (hvalue : ∀ x : Regular q, (R x).val = F x.val)
    (hD : ∀ x : Regular q, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) R x
      (ContinuousLinearMap.id ℝ Plane)) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F := by
  apply HolomorphicCurveMaps.contMDiff_of_mdifferentiable F
  apply MNEC.NativeRemovableMaps.mdifferentiable_of_continuous_off_finite F hc
    (zeroSet q) (zeroSet_finite q)
  intro x hx
  obtain ⟨a, ha⟩ := NativePhysicalDifferentialEquiv.primitive_translation_germ F R hR hvalue hD ⟨x, hx⟩
  exact NativePhysicalDifferentialEquiv.mdifferentiableAt_of_primitive_germ F hc
    ⟨x, hx⟩ (R ⟨x, hx⟩) (hvalue _) a ha

theorem pullback_eq (F : X → Y) (hHol : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (R : Regular q → Regular r) (hR : Continuous R)
    (hvalue : ∀ x : Regular q, (R x).val = F x.val)
    (hD : ∀ x : Regular q, HasMFDerivAt 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) R x
      (ContinuousLinearMap.id ℝ Plane)) : Jacobians.pullbackForm F hHol r.val = q.val := by
  apply form_eq_of_eqOn_regular q
  intro x hx
  obtain ⟨a, ha⟩ := NativePhysicalDifferentialEquiv.primitive_translation_germ F R hR hvalue hD ⟨x, hx⟩
  exact (NativePhysicalDifferentialEquiv.pullback_of_primitive_germ F hHol.continuous
    ⟨x, hx⟩ (R ⟨x, hx⟩) (hvalue _) a ha).symm

end VeechDichotomy.NativePhysicalHolomorphicMap
