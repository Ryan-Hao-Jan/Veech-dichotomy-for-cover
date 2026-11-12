module

public import VeechDichotomy.UniformBeltramiDisks
public import VeechDichotomy.DisjointPointTransport

/-! Explicit plane cutoff transports conjugated by the parameter-dependent
normalization. Both directions are jointly continuous and fix the
complement of ONE compact original coordinate disk. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiPlaneTransport

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiDiskData UniformBeltramiDisks
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} {b : X} {μ₀ : Parameter} {U : Set X} (D : Data q b μ₀ U)

abbrev Parameters := Near D × LocalTranslationPlane.Parameter

def transport (p : Parameters D) : ℂ ≃ₜ ℂ :=
  ((normalizedPlane D p.1).trans (LocalTranslationPlane.homeomorph p.2)).trans (normalizedPlane D p.1).symm

theorem transport_apply (p : Parameters D) (z : ℂ) : transport D p z =
    (normalizedPlane D p.1).symm (LocalTranslationPlane.homeomorph p.2 (normalizedPlane D p.1 z)) := rfl

theorem transport_inverse_apply (p : Parameters D) (z : ℂ) : (transport D p).symm z =
    (normalizedPlane D p.1).symm ((LocalTranslationPlane.homeomorph p.2).symm (normalizedPlane D p.1 z)) := rfl

theorem continuous_transport : Continuous (fun p : Parameters D × ℂ => transport D p.1 p.2) := by
  have hμ : Continuous (fun p : Parameters D × ℂ => p.1.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hδ : Continuous (fun p : Parameters D × ℂ => p.1.2) := continuous_snd.comp continuous_fst
  have hnorm : Continuous (fun p : Parameters D × ℂ => normalizedPlane D p.1.1 p.2) := by
    change Continuous (fun p : Parameters D × ℂ => BeltramiChartNormalization.plane q b D.radius D.radius_pos p.1.1.val p.2)
    exact Continuous.comp (f := fun p : Parameters D × ℂ => (p.1.1.val, p.2))
      (g := fun p : Parameter × ℂ => BeltramiChartNormalization.plane q b D.radius D.radius_pos p.1 p.2)
      (BeltramiChartNormalization.continuous_plane q b D.radius D.radius_pos) (hμ.prodMk continuous_snd)
  have hmove : Continuous (fun p : Parameters D × ℂ =>
      LocalTranslationPlane.homeomorph p.1.2 (normalizedPlane D p.1.1 p.2)) :=
    LocalTranslationContinuity.continuous_forward.comp (hδ.prodMk hnorm)
  change Continuous (fun p : Parameters D × ℂ =>
    (BeltramiChartNormalization.plane q b D.radius D.radius_pos p.1.1.val).symm
      (LocalTranslationPlane.homeomorph p.1.2 (normalizedPlane D p.1.1 p.2)))
  exact Continuous.comp (f := fun p : Parameters D × ℂ =>
    (p.1.1.val, LocalTranslationPlane.homeomorph p.1.2 (normalizedPlane D p.1.1 p.2)))
    (BeltramiChartNormalization.continuous_plane_inverse q b D.radius D.radius_pos) (hμ.prodMk hmove)

theorem continuous_inverse : Continuous (fun p : Parameters D × ℂ => (transport D p.1).symm p.2) := by
  have hμ : Continuous (fun p : Parameters D × ℂ => p.1.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hδ : Continuous (fun p : Parameters D × ℂ => p.1.2) := continuous_snd.comp continuous_fst
  have hnorm : Continuous (fun p : Parameters D × ℂ => normalizedPlane D p.1.1 p.2) := by
    change Continuous (fun p : Parameters D × ℂ => BeltramiChartNormalization.plane q b D.radius D.radius_pos p.1.1.val p.2)
    exact Continuous.comp (f := fun p : Parameters D × ℂ => (p.1.1.val, p.2))
      (g := fun p : Parameter × ℂ => BeltramiChartNormalization.plane q b D.radius D.radius_pos p.1 p.2)
      (BeltramiChartNormalization.continuous_plane q b D.radius D.radius_pos) (hμ.prodMk continuous_snd)
  have hmove : Continuous (fun p : Parameters D × ℂ =>
      (LocalTranslationPlane.homeomorph p.1.2).symm (normalizedPlane D p.1.1 p.2)) :=
    LocalTranslationContinuity.continuous_inverse.comp (hδ.prodMk hnorm)
  change Continuous (fun p : Parameters D × ℂ =>
    (BeltramiChartNormalization.plane q b D.radius D.radius_pos p.1.1.val).symm
      ((LocalTranslationPlane.homeomorph p.1.2).symm (normalizedPlane D p.1.1 p.2)))
  exact Continuous.comp (f := fun p : Parameters D × ℂ =>
    (p.1.1.val, (LocalTranslationPlane.homeomorph p.1.2).symm (normalizedPlane D p.1.1 p.2)))
    (BeltramiChartNormalization.continuous_plane_inverse q b D.radius D.radius_pos) (hμ.prodMk hmove)

theorem normalized_large (μ : Near D) {z : ℂ} (hz : z ∉ closedBall 0 D.oldRadius) :
    2 ≤ ‖normalizedPlane D μ z‖ := by
  by_contra h
  have hbound := inverse_plane_bound D μ (le_of_lt (lt_of_not_ge h))
  rw [Homeomorph.symm_apply_apply] at hbound
  exact hz (by rw [mem_closedBall, dist_zero_right]; exact hbound.le)

theorem fixed_outside (p : Parameters D) (z : ℂ) (hz : z ∉ closedBall 0 D.oldRadius) : transport D p z = z := by
  rw [transport_apply, LocalTranslationPlane.homeomorph_fixed p.2 (normalized_large D p.1 hz), Homeomorph.symm_apply_apply]

theorem inverse_fixed_outside (p : Parameters D) (z : ℂ) (hz : z ∉ closedBall 0 D.oldRadius) :
    (transport D p).symm z = z := ChartHomeomorphExtension.inverse_fixed (transport D p) (fixed_outside D p) hz

theorem preserves_target (p : Parameters D) :
    MapsTo (transport D p) (NativePowerCharts.chosen q b).chart.target (NativePowerCharts.chosen q b).chart.target :=
  DisjointPointTransport.mapsTo_of_fixed (transport D p) (fun z hz => fixed_outside D p z (fun hk => hz (D.old_target hk)))

theorem inverse_preserves_target (p : Parameters D) :
    MapsTo (transport D p).symm (NativePowerCharts.chosen q b).chart.target (NativePowerCharts.chosen q b).chart.target :=
  DisjointPointTransport.mapsTo_of_fixed (transport D p).symm (fun z hz => inverse_fixed_outside D p z (fun hk => hz (D.old_target hk)))

end VeechDichotomy.BeltramiPlaneTransport
