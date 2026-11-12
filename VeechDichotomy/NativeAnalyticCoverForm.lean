module

public import VeechDichotomy.HolomorphicCotangentForms
public import VeechDichotomy.NativeAnalyticCoverProjection

/-! The actual base differential pulls back to a holomorphic cotangent
section on the entire analytic family. Its pullback along every native
fiber inclusion is exactly the already constructed native differential,
including every critical point and every differential zero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticCoverForm

open MNEC.NativeAbelianDifferential NativeTranslationCover NativeAnalyticMarkTransport
open NativeAnalyticCoverTotalSpace NativeAnalyticCoverProjection ComplexDisplacementParameters
open HolomorphicCotangentForms Set
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y} {m : ℕ}
variable (π : Cover ωX ωY) {b : Fin m → X} (A : Data b) (hBranch : range b = branchValues π)

def form : Form (Space m × ℂ) (TotalSpace π A hBranch) :=
  pullback (map π A hBranch) (holomorphic_map π A hBranch) ωX.val

@[simp] theorem form_value (p : TotalSpace π A hBranch) : (form π A hBranch).toFun p =
    (ωX.val.toFun (map π A hBranch p)).comp
      (mfderiv 𝓘(ℂ, Space m × ℂ) 𝓘(ℂ) (map π A hBranch) p) := rfl

theorem fiber_pullback_eq (a : Parameters m) :
    pullback (NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a)
      (NativeAnalyticCoverFiberCharts.holomorphic_inclusion π b hBranch A a) (form π A hBranch) =
    (NativeLocalCoverFamily.differential π b hBranch A.marks (A.tuple a)).val := by
  rw [form, pullback_comp]
  have hmap : map π A hBranch ∘ NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a =
      (NativeLocalCoverFamily.cover π b hBranch A.marks (A.tuple a)).map :=
    funext fun z => (fiber_cover_map π A hBranch a z).symm
  apply ContMDiffSection.ext
  intro z
  change (ωX.val.toFun ((map π A hBranch ∘ NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a) z)).comp
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (map π A hBranch ∘ NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a) z) = _
  rw [hmap]
  exact (NativeTranslationCover.pullback_at (NativeLocalCoverFamily.cover π b hBranch A.marks (A.tuple a)) z).symm

theorem fiber_value (a : Parameters m) (z : NativeAnalyticCoverFiberCharts.Source π b hBranch A a) :
    ((form π A hBranch).toFun (NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a z)).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ, Space m × ℂ) (NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a) z) =
    (NativeLocalCoverFamily.differential π b hBranch A.marks (A.tuple a)).val.toFun z :=
  congrArg (fun α : Form ℂ (NativeAnalyticCoverFiberCharts.Source π b hBranch A a) => α.toFun z)
    (fiber_pullback_eq π A hBranch a)

theorem fiber_nonzero (a : Parameters m) :
    pullback (NativeAnalyticCoverFiberCharts.inclusion π b hBranch A a)
      (NativeAnalyticCoverFiberCharts.holomorphic_inclusion π b hBranch A a) (form π A hBranch) ≠ 0 := by
  rw [fiber_pullback_eq]
  exact (NativeLocalCoverFamily.differential π b hBranch A.marks (A.tuple a)).property

theorem form_nonzero : form π A hBranch ≠ 0 := by
  intro hzero
  apply fiber_nonzero π A hBranch (zero m)
  rw [hzero]
  exact map_zero _

end VeechDichotomy.NativeAnalyticCoverForm
