module

public import MNEC.NativePrimitiveAreaCharts
public import Jacobians.CanonicalForms.CanonicalFormDifferential
public import MNEC.OrientedLatticeRebasing
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian

/-! Actual original-chart Jacobians of arbitrary q-primitives. The native
cotangent identity and the genuine original-chart inverse derivative give
complex derivative coeffAt q. Its real physical determinant is normSq of
that coefficient, proved by the actual real multiplication matrix. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MNEC.NativePrimitiveJacobian

open LatticeTorus NativeAbelianDifferential NativePrimitiveTransitions NativeRegularTranslationAtlas
open NativePrimitiveAreaCharts Set Filter Topology
open scoped Manifold ContDiff Classical
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

def realMul (c : ℂ) : Plane →L[ℝ] Plane :=
  (toPlane.toContinuousLinearMap.comp ((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ)).comp
    toPlane.symm.toContinuousLinearMap

theorem realMul_apply (c : ℂ) (p : Plane) : realMul c p = toPlane (c * toPlane.symm p) := rfl

theorem realMul_det (c : ℂ) : (realMul c).det = Complex.normSq c := by
  change LinearMap.det (realMul c : Plane →ₗ[ℝ] Plane) = _
  rw [OrientedLatticeRebasing.linearMap_det_eq_cross]
  have h₁ : realMul c (1, 0) = (c.re, c.im) := by
    change toPlane (c * toPlane.symm (1, 0)) = _
    simp [toPlane, Complex.equivRealProdCLM_symm_apply]
  have h₂ : realMul c (0, 1) = (-c.im, c.re) := by
    change toPlane (c * toPlane.symm (0, 1)) = _
    simp [toPlane, Complex.equivRealProdCLM_symm_apply]
  change Twists.cross (realMul c (1, 0)) (realMul c (0, 1)) = _
  rw [h₁, h₂]
  simp only [Twists.cross, Complex.normSq_apply]
  ring

theorem realMul_abs_det (c : ℂ) : |(realMul c).det| = Complex.normSq c := by
  rw [realMul_det, abs_of_nonneg (Complex.normSq_nonneg c)]

theorem original_complex_derivative (q : Differential X) (b : X) (i : Index q) (z : ℂ)
    (hz : z ∈ (chartAt ℂ b).target) (hy : (chartAt ℂ b).symm z ∈ i.2.chart.source) :
    HasFDerivAt (i.2.chart ∘ (chartAt ℂ b).symm)
      (Jacobians.NativeCanonical.coeffAt q.val b z • ContinuousLinearMap.id ℂ ℂ) z := by
  let e := chartAt ℂ b
  let y := e.symm z
  have hyE : y ∈ e.source := e.map_target hz
  have hInv := (mdifferentiableAt_atlas_symm (I := 𝓘(ℂ)) (chart_mem_atlas ℂ b) hz).hasMFDerivAt
  have hcomp := (i.2.derivative y hy).comp z hInv
  have hdiff : DifferentiableAt ℂ (i.2.chart ∘ e.symm) z := by
    simpa only [Function.comp_def, e] using! hcomp.hasFDerivAt.differentiableAt
  let frame := (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) b).symmL ℂ y 1
  have hfr : Jacobians.Montel.localRep q.val b y = deriv (i.2.chart ∘ e.symm) (e y) := by
    have h := Jacobians.Dolbeault.mfderiv_apply_symmL_eq_deriv (i.2.chart) hyE
      (i.2.derivative y hy).mdifferentiableAt
    have hm := DFunLike.congr_fun (i.2.derivative y hy).mfderiv frame
    let J := NormedSpace.fromTangentSpace (𝕜 := ℂ) (i.2.chart y)
    have hmC := congrArg J hm
    have hC := congrArg J h
    have hEq := hmC.symm.trans hC
    simpa only [J, NormedSpace.fromTangentSpace, tangentSpaceCastModel, frame,
      Jacobians.Montel.localRep, e] using! hEq
  have hc : deriv (i.2.chart ∘ e.symm) z = Jacobians.NativeCanonical.coeffAt q.val b z := by
    change deriv (i.2.chart ∘ e.symm) z = Jacobians.Montel.localRep q.val b y
    calc
      _ = deriv (i.2.chart ∘ e.symm) (e y) := congrArg (deriv (i.2.chart ∘ e.symm)) (e.right_inv hz).symm
      _ = Jacobians.Montel.localRep q.val b y := hfr.symm
  have hD : HasDerivAt (i.2.chart ∘ e.symm) (Jacobians.NativeCanonical.coeffAt q.val b z) z := hc ▸ hdiff.hasDerivAt
  apply hasFDerivAt_iff_hasDerivAt.mpr
  simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using hD
theorem real_conjugate_derivative (F : ℂ → ℂ) (c : ℂ) (p : Plane)
    (hF : HasFDerivAt F (c • ContinuousLinearMap.id ℂ ℂ) (toPlane.symm p)) :
    HasFDerivAt (fun y : Plane => toPlane (F (toPlane.symm y))) (realMul c) p := by
  have hR := hF.restrictScalars ℝ
  have h₁ := toPlane.toContinuousLinearMap.hasFDerivAt.comp (toPlane.symm p) hR
  have h₂ := h₁.comp p toPlane.symm.toContinuousLinearMap.hasFDerivAt
  simpa only [Function.comp_def, realMul] using! h₂

def originalCoordinate (q : Differential X) (b : X) : OpenPartialHomeomorph (Regular q) Plane :=
  ((chartAt ℂ b).subtypeRestr (s := regularOpen q) (regular_nonempty q)).transHomeomorph toPlane.toHomeomorph

theorem originalCoordinate_source (q : Differential X) (b : X) :
    (originalCoordinate q b).source = Subtype.val ⁻¹' (chartAt ℂ b).source :=
  (chartAt ℂ b).subtypeRestr_source (s := regularOpen q) (regular_nonempty q)

theorem originalCoordinate_apply (q : Differential X) (b : X) (x : Regular q) :
    originalCoordinate q b x = toPlane ((chartAt ℂ b) x.val) := rfl

theorem originalCoordinate_target_subset (q : Differential X) (b : X) :
    (originalCoordinate q b).target ⊆ toPlane.symm ⁻¹' (chartAt ℂ b).target := by
  intro p hp
  exact (chartAt ℂ b).subtypeRestr_target_subset (regular_nonempty q) hp

theorem originalCoordinate_symm_value (q : Differential X) (b : X) (p : Plane)
    (hp : p ∈ (originalCoordinate q b).target) :
    ((originalCoordinate q b).symm p).val = (chartAt ℂ b).symm (toPlane.symm p) := by
  let y := (originalCoordinate q b).symm p
  have hy : y.val ∈ (chartAt ℂ b).source := by
    have h := (originalCoordinate q b).map_target hp
    rwa [originalCoordinate_source] at h
  have heq : toPlane ((chartAt ℂ b) y.val) = p := (originalCoordinate q b).right_inv hp
  have hraw : (chartAt ℂ b) y.val = toPlane.symm p := by
    apply toPlane.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact heq
  calc
    y.val = (chartAt ℂ b).symm ((chartAt ℂ b) y.val) := ((chartAt ℂ b).left_inv hy).symm
    _ = _ := by rw [hraw]

def transition (q : Differential X) (b : X) (i : Index q) : OpenPartialHomeomorph Plane Plane :=
  (originalCoordinate q b).symm.trans (chart q i)

theorem transition_derivative (q : Differential X) (b : X) (i : Index q) (p : Plane)
    (hp : p ∈ (transition q b i).source) :
    HasFDerivAt (transition q b i)
      (realMul (Jacobians.NativeCanonical.coeffAt q.val b (toPlane.symm p))) p := by
  have hz := originalCoordinate_target_subset q b hp.1
  have hy : (chartAt ℂ b).symm (toPlane.symm p) ∈ i.2.chart.source := by
    have h := hp.2
    rw [chart_source] at h
    change ((originalCoordinate q b).symm p).val ∈ i.2.chart.source at h
    rwa [originalCoordinate_symm_value q b p hp.1] at h
  have hComplex := original_complex_derivative q b i (toPlane.symm p) hz hy
  have hReal := real_conjugate_derivative _ _ p hComplex
  have heq : (transition q b i : Plane → Plane) =ᶠ[𝓝 p]
      (fun y : Plane => toPlane (i.2.chart ((chartAt ℂ b).symm (toPlane.symm y)))) := by
    filter_upwards [(originalCoordinate q b).open_target.mem_nhds hp.1] with y hy
    change toPlane (i.2.chart ((originalCoordinate q b).symm y).val) = _
    rw [originalCoordinate_symm_value q b y hy]
  exact hReal.congr_of_eventuallyEq heq

end MNEC.NativePrimitiveJacobian
