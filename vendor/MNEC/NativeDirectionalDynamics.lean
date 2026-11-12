module

public import MNEC.NativeRegularTranslationAtlas
public import MNEC.TranslationAtlasCurves

/-! Actual directional fields and native maximal trajectories of an arbitrary
genuine holomorphic differential on its regular locus. Every geometric
instance is constructed by the proved primitive-chart atlas; only the
native differential/compact connected curve are inputs. Completeness,
canonical area and normalized probability are separate later boundaries. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeDirectionalDynamics

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas Set Topology
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
def field (q : Differential X) (v : Plane) : letI := chartedSpace q; ∀ x : (Regular q), TangentSpace 𝓘(ℝ, Plane) x := by
  let := chartedSpace q
  exact TranslationAtlasField.field v

theorem field_eq_const (q : Differential X) (v : Plane) (x : (Regular q)) : letI := chartedSpace q; field q v x = v := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationAtlasField.field_eq_const v x

theorem contMDiff_field (q : Differential X) (v : Plane) :
    letI := chartedSpace q
    letI : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
    ContMDiff 𝓘(ℝ, Plane) (𝓘(ℝ, Plane)).tangent ∞ (fun x : (Regular q) => (⟨x, field q v x⟩ : TangentBundle 𝓘(ℝ, Plane) (Regular q))) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationAtlasField.contMDiff_field v

theorem coordinate_formula (q : Differential X) (v : Plane) (i : Regular q) (x : (Regular q)) (hx : x ∈ (coordinateChart q i).source) :
    letI := chartedSpace q
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (coordinateChart q i) x (field q v x) = v := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  have hmem : coordinateChart q i ∈ atlas Plane (Regular q) := ⟨i, rfl⟩
  exact TranslationAtlasField.coordinate_formula (X := (Regular q)) v (coordinateChart q i) hmem x hx

def localTimeDomain (q : Differential X) (i : Regular q) (v : Plane) (x : (Regular q)) : Set ℝ :=
  TranslationAtlasCurves.timeDomain (coordinateChart q i) v x

def localCurve (q : Differential X) (i : Regular q) (v : Plane) (x : (Regular q)) : ℝ → (Regular q) :=
  TranslationAtlasCurves.curve (coordinateChart q i) v x

theorem localCurve_isMIntegralCurveOn (q : Differential X) (i : Regular q) (v : Plane) (x : (Regular q)) :
    letI := chartedSpace q
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (localCurve q i v x) (field q v) (localTimeDomain q i v x) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  have hmem : coordinateChart q i ∈ atlas Plane (Regular q) := ⟨i, rfl⟩
  exact TranslationAtlasCurves.isMIntegralCurveOn_curve (X := (Regular q)) (coordinateChart q i) hmem v x

def domain (q : Differential X) (v : Plane) (x : (Regular q)) : Set ℝ := by
  let := chartedSpace q
  exact TranslationAtlasCurves.domain v x

def trajectory (q : Differential X) (v : Plane) (x : (Regular q)) : ℝ → (Regular q) := by
  let := chartedSpace q
  exact TranslationAtlasCurves.trajectory v x

theorem domain_open (q : Differential X) (v : Plane) (x : (Regular q)) : IsOpen (domain q v x) := by
  let := chartedSpace q
  exact TranslationAtlasCurves.domain_open v x

theorem domain_ordConnected (q : Differential X) (v : Plane) (x : (Regular q)) : OrdConnected (domain q v x) := by
  let := chartedSpace q
  exact TranslationAtlasCurves.domain_ordConnected v x

theorem domain_convex (q : Differential X) (v : Plane) (x : (Regular q)) : Convex ℝ (domain q v x) := by
  let := chartedSpace q
  exact TranslationAtlasCurves.domain_convex v x

theorem zero_mem_domain (q : Differential X) (v : Plane) (x : (Regular q)) : 0 ∈ domain q v x := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationAtlasCurves.zero_mem_domain v x

theorem trajectory_initial (q : Differential X) (v : Plane) (x : (Regular q)) : trajectory q v x 0 = x := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let : T2Space (Regular q) := inferInstance
  exact TranslationAtlasCurves.trajectory_initial v x

theorem trajectory_isMIntegralCurveOn (q : Differential X) (v : Plane) (x : (Regular q)) :
    letI := chartedSpace q
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) (trajectory q v x) (field q v) (domain q v x) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let : T2Space (Regular q) := inferInstance
  exact TranslationAtlasCurves.trajectory_isMIntegralCurveOn v x

theorem domain_connected (q : Differential X) (v : Plane) (x : (Regular q)) : IsConnected (domain q v x) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  exact TranslationAtlasCurves.domain_connected v x

theorem extends_every_open_interval (q : Differential X) (v : Plane) (x : (Regular q)) (U : Set ℝ) (γ : ℝ → (Regular q))
    (hU : IsOpen U) (hord : OrdConnected U) (hzero : 0 ∈ U) (hγzero : γ 0 = x) :
    letI := chartedSpace q
    IsMIntegralCurveOn (I := 𝓘(ℝ, Plane)) γ (field q v) U →
      U ⊆ domain q v x ∧ EqOn (trajectory q v x) γ U := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let : T2Space (Regular q) := inferInstance
  exact TranslationAtlasCurves.extends_every_open_interval v x U γ hU hord hzero hγzero

theorem domain_at_time (q : Differential X) (v : Plane) (x : (Regular q)) (t : ℝ) (ht : t ∈ domain q v x) :
    domain q v (trajectory q v x t) = {s | s + t ∈ domain q v x} := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let : T2Space (Regular q) := inferInstance
  exact TranslationAtlasCurves.domain_at_time v x t ht

theorem trajectory_add (q : Differential X) (v : Plane) (x : (Regular q)) (t : ℝ) (ht : t ∈ domain q v x) (s : ℝ)
    (hs : s ∈ domain q v (trajectory q v x t)) :
    trajectory q v (trajectory q v x t) s = trajectory q v x (s + t) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let : T2Space (Regular q) := inferInstance
  exact TranslationAtlasCurves.trajectory_add v x t ht s hs

theorem reverse_time (q : Differential X) (v : Plane) (x : (Regular q)) (t : ℝ) (ht : t ∈ domain q v x) :
    -t ∈ domain q v (trajectory q v x t) ∧ trajectory q v (trajectory q v x t) (-t) = x := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let : T2Space (Regular q) := inferInstance
  exact TranslationAtlasCurves.reverse_time v x t ht

/-- Genuine physical straightness in the constructed primitive coordinates. -/
theorem local_physical_straightness (q : Differential X) (i : Regular q) (v : Plane) (x : Regular q)
    (hx : x ∈ (coordinateChart q i).source) :
    ∃ ε > 0, ∀ t ∈ Metric.ball (0 : ℝ) ε, t ∈ domain q v x ∧
      coordinateChart q i (trajectory q v x t) = coordinateChart q i x + t • v := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  have he : coordinateChart q i ∈ atlas Plane (Regular q) := ⟨i, rfl⟩
  exact TranslationAtlasCurves.local_physical_straightness (X := Regular q) (coordinateChart q i) he v x hx

/-- The observed trajectory on the ORIGINAL complex curve is explicitly an
inverse primitive of q applied to the actual physical straight line. -/
theorem local_primitive_straightness (q : Differential X) (i : Regular q) (v : Plane) (x : Regular q)
    (hx : x ∈ (coordinateChart q i).source) :
    ∃ ε > 0, ∀ t ∈ Metric.ball (0 : ℝ) ε, t ∈ domain q v x ∧
      trajectory q v x t ∈ (coordinateChart q i).source ∧
      (trajectory q v x t).val = (primitiveChart q i).symm
        (toPlane.symm (coordinateChart q i x + t • v)) := by
  let := chartedSpace q
  let : IsManifold 𝓘(ℝ, Plane) ∞ (Regular q) := NativeRegularTranslationAtlas.isManifold q ∞
  let : HasGroupoid (Regular q) TranslationGroupoid.groupoid := has_translation_groupoid q
  let e := coordinateChart q i
  have he : e ∈ atlas Plane (Regular q) := ⟨i, rfl⟩
  obtain ⟨ε, hε, hrep⟩ := TranslationAtlasCurves.local_representation e he v x hx
  refine ⟨ε, hε, fun t ht => ?_⟩
  obtain ⟨hD, hline, hcurve⟩ := hrep t ht
  have heq : trajectory q v x t = e.symm (e x + t • v) := hcurve
  refine ⟨hD, heq ▸ e.map_target hline, ?_⟩
  exact (congrArg Subtype.val heq).trans (coordinateChart_symm_value q i _ hline)

end MNEC.NativeDirectionalDynamics
