module

public import VeechDichotomy.PhysicalDerivativeAffine
public import VeechDichotomy.NativeShearMatrices
public import VeechDichotomy.NativePrimitiveRectangles
public import VeechDichotomy.BeltramiMarkedLimitRectangles

/-! Near an ACTUAL regular fixed point, a native lower-shear affine
automorphism is the actual vertical flow with its computed transverse
time displacement. The local clock is continuous and nonconstant in
every neighborhood when the shear is nonzero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeShearClockGerms

open MNEC.LatticeTorus MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open MNEC.NativeDirectionalDynamics MNEC.NativeCompleteDirectionalFlow
open NativeVeech NativePrimitiveRectangles NativeShearMatrices Set Filter Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (q : Differential X)

def clock (p : Regular q) (a : ℝ) (y : Regular q) : ℝ :=
  a * ((coordinateChart q p y).1 - (coordinateChart q p p).1)

theorem clock_self (p : Regular q) (a : ℝ) : clock q p a p = 0 := by simp [clock]

theorem clock_continuousOn (p : Regular q) (a : ℝ) :
    ContinuousOn (clock q p a) (coordinateChart q p).source :=
  continuousOn_const.mul ((coordinateChart q p).continuousOn.fst.sub continuousOn_const)

theorem clock_nearby_nonzero (p : Regular q) {a : ℝ} (ha : a ≠ 0)
    (U : Set (Regular q)) (hU : IsOpen U) (hpU : p ∈ U) : ∃ y ∈ U, clock q p a y ≠ 0 := by
  let c := coordinateChart q p
  have hp : p ∈ c.source := coordinateChart_center q p
  have hW : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.symm.continuousOn.isOpen_inter_preimage c.open_target hU
  have hpW : c p ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hp, by simpa only [mem_preimage, c.left_inv hp] using hpU⟩
  obtain ⟨l, r, b, t, hpR, hR⟩ := BeltramiMarkedLimitRectangles.closed_rectangle_in_open (c p) hW hpW
  let z : Plane := (((c p).1 + r) / 2, (c p).2)
  have hzR : z ∈ Icc l r ×ˢ Icc b t :=
    ⟨⟨by dsimp [z]; linarith [hpR.1.1, hpR.1.2], by dsimp [z]; linarith [hpR.1.2]⟩,
      ⟨hpR.2.1.le, hpR.2.2.le⟩⟩
  have hzW := hR hzR
  refine ⟨c.symm z, hzW.2, ?_⟩
  change a * ((c (c.symm z)).1 - (c p).1) ≠ 0
  rw [c.right_inv hzW.1]
  apply mul_ne_zero ha
  dsimp [z]
  linarith [hpR.1.2]

local instance : ChartedSpace Plane (Regular q) := chartedSpace q
local instance : HasGroupoid (Regular q) MNEC.TranslationGroupoid.groupoid := has_translation_groupoid q
local instance : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := isManifold q ∞

theorem local_clock {a : ℝ} (φ : AffineAutomorphism q (lower a)) (p : Regular q) (hfix : φ.regular p = p) :
    ∀ᶠ y in 𝓝 p, φ.regular y = trajectory q vertical y (clock q p a y) := by
  let c := coordinateChart q p
  have hp : p ∈ c.source := coordinateChart_center q p
  have hi : c ∈ atlas Plane (Regular q) := ⟨p, rfl⟩
  have hfp : φ.regular p ∈ c.source := by rwa [hfix]
  have hAffine := PhysicalDerivativeAffine.map_affine_germ φ.regular φ.regular.continuous (linear (lower a))
    φ.derivative c c hi hi p hp hfp
  simp only [hfix] at hAffine
  obtain ⟨l, r, b, t, hpR, hRclosed⟩ := BeltramiMarkedLimitRectangles.closed_rectangle_in_open (c p) c.open_target (c.map_source hp)
  have hR : rectangle l r b t ⊆ c.target := fun z hz =>
    hRclosed ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hrectOpen : IsOpen (rectangle l r b t) := isOpen_Ioo.prod isOpen_Ioo
  have hnearR := (c.continuousAt hp).tendsto (hrectOpen.mem_nhds hpR)
  have hφlim : Tendsto φ.regular (𝓝 p) (𝓝 p) := by simpa only [hfix] using φ.regular.continuous.continuousAt.tendsto (x := p)
  filter_upwards [hAffine, c.open_source.mem_nhds hp, hφlim (c.open_source.mem_nhds hp), hnearR, hφlim hnearR]
    with y hyA hyS hyφS hyR hyφR
  have hcoord : c (φ.regular y) = ((c y).1, (c y).2 + clock q p a y) := by
    rw [hyA, linear_action, linear_action]
    apply Prod.ext <;> dsimp [clock, c] <;> ring
  have htime : clock q p a y ∈ Ioo (b - (c y).2) (t - (c y).2) := by
    have hsecond := congrArg Prod.snd hcoord
    change (c (φ.regular y)).2 = (c y).2 + clock q p a y at hsecond
    constructor <;> linarith [hyφR.2.1, hyφR.2.2]
  have hseg := NativePrimitiveRectangles.vertical_interval q (MNEC.NativePrimitiveAreaCharts.selectedIndex q p) hR y hyS hyR
  calc
    φ.regular y = c.symm (c (φ.regular y)) := (c.left_inv hyφS).symm
    _ = c.symm ((c y).1, (c y).2 + clock q p a y) := congrArg c.symm hcoord
    _ = trajectory q vertical y (clock q p a y) := (hseg.2 _ htime).symm

end VeechDichotomy.NativeShearClockGerms
