module

public import MNEC.NativeCriticalRays
public import MNEC.NativePrimitiveEndpoint
public import MNEC.NativeTrajectoryZeroLimit
public import MNEC.NativeEndpointTimes
public import MNEC.NativeCompleteDirectionalFlow

/-! Almost-everywhere completeness of the ACTUAL native directional flow
of an arbitrary original holomorphic differential. An incomplete domain
has an actual excluded finite boundary, and compact regular continuation
forces a derived limiting zero. Its FIXED local primitive is affine on
a genuine connected tail; an actual rational time therefore hits that
zero's fixed null critical set. Countably many true partial preimages
are null. No endpoint/escape/primitive/affinity/nullness/completeness
certificate is an input to the final theorem. -/

@[expose] public section
noncomputable section
namespace MNEC.NativeConullDirectionalOrbits

open LatticeTorus NativeAbelianDifferential NativeRegularTranslationAtlas NativeDirectionalDynamics
open NativeCompleteDirectionalFlow NativeCriticalRays MeasureTheory Set Filter Topology
open scoped Classical Manifold ContDiff

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

theorem incomplete_mem_badSet (q : Differential X) (v : Plane) (x : Regular q)
    (hx : x ∉ completeOrbitSet q v) : x ∈ badSet q v := by
  have hproper : domain q v x ≠ univ := hx
  obtain ⟨B, hBoundary, hB⟩ := NativeEndpointTimes.exists_excluded_boundary q v x hproper
  obtain ⟨z, hz, hlim⟩ := NativeTrajectoryZeroLimit.exists_zero_limit q v x B hB hBoundary
  let p : Zero q := ⟨z, hz⟩
  let d := datum q p
  have hstay : ∀ᶠ t in 𝓝[domain q v x] B, (trajectory q v x t).val ∈ d.U :=
    hlim (d.open_U.mem_nhds d.center)
  obtain ⟨I, hI, hconvex, hD, hfilter, hstayI, a, ha⟩ :=
    NativeEndpointTimes.rational_tail q v x B hBoundary d.U hstay
  let : NeBot (𝓝[domain q v x] B) := mem_closure_iff_nhdsWithin_neBot.mp hBoundary
  let : NeBot (𝓝[I] B) := by rw [hfilter]; infer_instance
  have hlimI : Tendsto (fun t : ℝ => (trajectory q v x t).val) (𝓝[I] B) (𝓝 p.val) := by
    rw [hfilter]
    exact hlim
  have hline := NativePrimitiveEndpoint.endpoint_tail_in_linePreimage q v x d.U d.open_U d.F
    d.derivative I hI hconvex hD hstayI B p.val d.center d.Fzero hlimI (a : ℝ) ha
  exact mem_badSet_of_linePreimage_hit q v p a x (hD ha) hline

/-- Only the genuine original q and a nonzero physical direction are inputs. -/
theorem ae_complete (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    ∀ᵐ x ∂NativeRegularArea.regularArea q, x ∈ completeOrbitSet q v := by
  filter_upwards [ae_not_mem_badSet q v hv] with x hx
  by_contra hcomp
  exact hx (incomplete_mem_badSet q v x hcomp)

theorem completeSet_ae_eq_univ (q : Differential X) (v : Plane) (hv : v ≠ 0) :
    completeOrbitSet q v =ᵐ[NativeRegularArea.regularArea q] univ := by
  filter_upwards [ae_complete q v hv] with x hx
  exact propext ⟨fun _ => mem_univ _, fun _ => hx⟩

end MNEC.NativeConullDirectionalOrbits

