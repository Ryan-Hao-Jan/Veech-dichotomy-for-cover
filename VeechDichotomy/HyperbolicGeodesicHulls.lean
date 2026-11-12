module

public import VeechDichotomy.HyperbolicKleinGeodesics
public import Mathlib.Analysis.Convex.Topology

/-! Actual intrinsic geodesic convexity and convex hulls in the Poincare
upper half-plane. The proved Klein-segment identity identifies these
with ordinary convexity and convex hulls. Finite hulls are genuinely
compact, and actual SL2 isometries transport the entire hull exactly. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.HyperbolicGeodesicHulls

open LinearGroup Set Topology HyperbolicMetricSegments HyperbolicKleinMap
open HyperbolicKleinHomeomorph
open scoped UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

def GeodesicallyConvex (S : Set ℍ) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → metricSegment a b ⊆ S

theorem point_injective : Function.Injective point := fun _ _ h =>
  homeomorph.injective (Subtype.ext h)

theorem point_range : range point = Metric.ball (0 : ℂ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one z
  · intro u hu
    let v : Disk := ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu⟩
    exact ⟨inverse v, congrArg Subtype.val (forward_inverse v)⟩

theorem point_isEmbedding : IsEmbedding point :=
  IsEmbedding.subtypeVal.comp homeomorph.isEmbedding

theorem geodesicallyConvex_iff (S : Set ℍ) :
    GeodesicallyConvex S ↔ Convex ℝ (point '' S) := by
  constructor
  · intro hS
    apply convex_iff_segment_subset.mpr
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ u hu
    rw [← HyperbolicKleinGeodesics.image_metricSegment] at hu
    obtain ⟨z, hz, rfl⟩ := hu
    exact ⟨z, hS ha hb hz, rfl⟩
  · intro hS a ha b hb z hz
    have hpz := (HyperbolicKleinGeodesics.mem_metricSegment_iff a b z).mp hz
    obtain ⟨w, hw, he⟩ := hS.segment_subset ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hpz
    exact point_injective he ▸ hw

def hull (S : Set ℍ) : Set ℍ := point ⁻¹' convexHull ℝ (point '' S)

theorem convexHull_subset_ball (S : Set ℍ) :
    convexHull ℝ (point '' S) ⊆ Metric.ball (0 : ℂ) 1 := by
  apply convexHull_min _ (convex_ball _ _)
  rintro _ ⟨z, _, rfl⟩
  simpa only [Metric.mem_ball, dist_zero_right] using norm_point_lt_one z

theorem image_hull (S : Set ℍ) : point '' hull S = convexHull ℝ (point '' S) := by
  apply image_preimage_eq_of_subset
  rw [point_range]
  exact convexHull_subset_ball S

theorem subset_hull (S : Set ℍ) : S ⊆ hull S := by
  intro z hz
  exact subset_convexHull ℝ _ ⟨z, hz, rfl⟩

theorem geodesicallyConvex_hull (S : Set ℍ) : GeodesicallyConvex (hull S) := by
  rw [geodesicallyConvex_iff, image_hull]
  exact convex_convexHull ℝ _

theorem hull_min {S T : Set ℍ} (hST : S ⊆ T) (hT : GeodesicallyConvex T) : hull S ⊆ T := by
  intro z hz
  have hpz : point z ∈ point '' T :=
    convexHull_min (image_mono hST) ((geodesicallyConvex_iff T).mp hT) hz
  obtain ⟨w, hw, he⟩ := hpz
  exact point_injective he ▸ hw

theorem hull_mono {S T : Set ℍ} (hST : S ⊆ T) : hull S ⊆ hull T :=
  hull_min (hST.trans (subset_hull T)) (geodesicallyConvex_hull T)

theorem hull_eq_self {S : Set ℍ} (hS : GeodesicallyConvex S) : hull S = S :=
  (hull_min Subset.rfl hS).antisymm (subset_hull S)

theorem geodesicallyConvex_smul (A : SL2) {S : Set ℍ} (hS : GeodesicallyConvex S) :
    GeodesicallyConvex ((fun z : ℍ => A • z) '' S) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ z hz
  rw [← HyperbolicMetricSegments.image_metricSegment] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hS ha hb hw, rfl⟩

theorem hull_smul_subset (A : SL2) (S : Set ℍ) :
    hull ((fun z : ℍ => A • z) '' S) ⊆ (fun z : ℍ => A • z) '' hull S :=
  hull_min (image_mono (subset_hull S)) (geodesicallyConvex_smul A (geodesicallyConvex_hull S))

theorem image_hull_smul (A : SL2) (S : Set ℍ) :
    (fun z : ℍ => A • z) '' hull S = hull ((fun z : ℍ => A • z) '' S) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hback : hull S ⊆ (fun w : ℍ => A⁻¹ • w) '' hull ((fun w : ℍ => A • w) '' S) := by
      simpa only [image_image, inv_smul_smul, image_id'] using
        hull_smul_subset A⁻¹ ((fun w : ℍ => A • w) '' S)
    obtain ⟨w, hw, he⟩ := hback hz
    have haw : A • z = w := by rw [← he, smul_inv_smul]
    change A • z ∈ hull ((fun z : ℍ => A • z) '' S)
    rwa [haw]
  · exact hull_smul_subset A S

theorem isCompact_hull {S : Set ℍ} (hS : S.Finite) : IsCompact (hull S) := by
  apply point_isEmbedding.isCompact_iff.mpr
  rw [image_hull]
  exact (hS.image point).isCompact_convexHull ℝ

theorem isClosed_hull {S : Set ℍ} (hS : S.Finite) : IsClosed (hull S) :=
  (isCompact_hull hS).isClosed

theorem hull_pair (a b : ℍ) : hull {a, b} = metricSegment a b := by
  ext z
  change point z ∈ convexHull ℝ (point '' {a, b}) ↔ _
  rw [image_pair, convexHull_pair, HyperbolicKleinGeodesics.mem_metricSegment_iff]

end VeechDichotomy.HyperbolicGeodesicHulls
