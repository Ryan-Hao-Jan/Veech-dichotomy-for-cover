module

public import VeechDichotomy.NativeAnalyticMarkTransport
public import VeechDichotomy.AnalyticTransportSmoothCompositions
public import VeechDichotomy.NativeLocalCoverRegularCharts

/-! Joint analytic mixed-transition expressions for the actual moving
cover construction, in both directions. Inverse transport is explicitly
holomorphic near the image of every marked inner disk, and the original
unramified local cover inverse is genuinely holomorphic. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.AnalyticCoverTransitionExpressions

open MNEC.NativeAbelianDifferential NativeTranslationCover RelocatedCoverCharts
open NativeAnalyticMarkTransport ComplexDisplacementParameters AnalyticTransportCoordinates
open AnalyticTransportCompositions HolomorphicCurveGerms PointTransportUniform
open Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b)

theorem oldLocalMap_holomorphic (y : RegularPoint π) : (oldLocalMap π y).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  apply NativeMovingCoverRegularity.local_chart_holomorphic π (Homeomorph.refl X) (oldLocalMap π y)
  · exact fun z _ => localMap_apply π (Homeomorph.refl X) y z
  · exact fun _ _ => π.holomorphic.mdifferentiableAt (by decide)
  · intro z hz
    exact localMap_source_noncritical π (Homeomorph.refl X) y hz

def forward (c : OpenPartialHomeomorph Y ℂ) (d : OpenPartialHomeomorph X ℂ) (p : Space m × ℂ) :
    Space m × ℂ := (p.1, d (ambientTransport A.combined p.1 (π.map (c.symm p.2))))

def inverse (y : RegularPoint π) (c : OpenPartialHomeomorph Y ℂ) (d : OpenPartialHomeomorph X ℂ)
    (p : Space m × ℂ) : Space m × ℂ :=
  (p.1, c ((oldLocalMap π y).symm ((ambientTransport A.combined p.1).symm (d.symm p.2))))

theorem forward_contDiffAt (c : OpenPartialHomeomorph Y ℂ) (d : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (hd : d.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (p : Space m × ℂ) (ha : p.1 ∈ domain m) (hp : p.2 ∈ c.target) (i : Fin m)
    (hi : π.map (c.symm p.2) ∈ innerDisk (A.disks i))
    (hout : ambientTransport A.combined p.1 (π.map (c.symm p.2)) ∈ d.source) :
    ContDiffAt ℂ ω (forward π A c d) p := by
  have hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (π.map ∘ c.symm) p.2 :=
    (π.holomorphic (c.symm p.2)).comp p.2 (chart_contMDiffAt_symm c hc hp)
  have hg := chart_contMDiffAt d hd hout
  exact contDiffAt_fst.prodMk (AnalyticTransportSmoothCompositions.forward_contDiffAt
    A.disks A.combined A.restriction i (A.holomorphic i) (π.map ∘ c.symm) d p ha hi hf hg)

theorem inverse_contDiffAt (y : RegularPoint π) (c : OpenPartialHomeomorph Y ℂ) (d : OpenPartialHomeomorph X ℂ)
    (hc : c.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)) (hd : d.MDifferentiable 𝓘(ℂ) 𝓘(ℂ))
    (p : Space m × ℂ) (ha : p.1 ∈ domain m) (hp : p.2 ∈ d.target)
    (ht : (ambientTransport A.combined p.1).symm (d.symm p.2) ∈ (oldLocalMap π y).target)
    (hout : (oldLocalMap π y).symm ((ambientTransport A.combined p.1).symm (d.symm p.2)) ∈ c.source)
    (i : Fin m) (hi : π.map ((oldLocalMap π y).symm
      ((ambientTransport A.combined p.1).symm (d.symm p.2))) ∈ innerDisk (A.disks i)) :
    ContDiffAt ℂ ω (inverse π A y c d) p := by
  let v := (ambientTransport A.combined p.1).symm (d.symm p.2)
  have hv : π.map ((oldLocalMap π y).symm v) = v := by
    have h := (oldLocalMap π y).right_inv ht
    change localMap π (Homeomorph.refl X) y ((oldLocalMap π y).symm v) = v at h
    rwa [localMap_apply] at h
  have hvInner : v ∈ innerDisk (A.disks i) := by rwa [hv] at hi
  have himage := image_conditions A.disks A.combined A.restriction ha i hvInner
  rw [Homeomorph.apply_symm_apply] at himage
  let g := (oldLocalMap π y).symm.trans c
  have hg : g.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := (oldLocalMap_holomorphic π y).symm.trans hc
  have hgs : v ∈ g.source := ⟨ht, hout⟩
  have hinner := AnalyticTransportSmoothCompositions.inverse_contDiffAt A.disks A.combined A.restriction
    i (A.holomorphic i) d.symm g p ha himage.1 himage.2 (chart_contMDiffAt_symm d hd hp)
    (chart_contMDiffAt g hg hgs)
  exact contDiffAt_fst.prodMk hinner

end VeechDichotomy.AnalyticCoverTransitionExpressions
