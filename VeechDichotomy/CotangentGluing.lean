module

/-
Generic analytic cotangent-section gluing, adapted from the supplied
MNEC/NativeCoefficientGluing.lean. That source credits the jacobian-challenge
project, commit 8ce1ec28aed1c78b3b39d0bae26e2858c82f5143 (Apache-2.0).

Compactness, connectedness and Hausdorff assumptions have been removed;
the proved output is an actual analytic cotangent section on any complex
curve. The original proof is rechecked in this more general setting.
Source hashes and adaptation details are recorded in provenance JSON.
-/

public import VeechDichotomy.NativeSurface

@[expose] public section

open scoped Manifold ContDiff Bundle Topology
open Set Filter

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace VeechDichotomy.CotangentGluing

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

abbrev HolomorphicForm :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)

structure Coefficients where
  coeff : X → ℂ → ℂ
  analytic : ∀ x, AnalyticOnNhd ℂ (coeff x) (extChartAt 𝓘(ℂ) x).target
  cocycle : ∀ x x' z, z ∈ (extChartAt 𝓘(ℂ) x).target →
    (extChartAt 𝓘(ℂ) x).symm z ∈ (extChartAt 𝓘(ℂ) x').source →
    coeff x z = coeff x' ((extChartAt 𝓘(ℂ) x') ((extChartAt 𝓘(ℂ) x).symm z)) *
      (fderiv ℂ ((extChartAt 𝓘(ℂ) x') ∘ (extChartAt 𝓘(ℂ) x).symm) z) 1

variable {X}

noncomputable def rawCLM (form : Coefficients X) (x y : X) :
    TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y :=
  (form.coeff x ((extChartAt 𝓘(ℂ, ℂ) x) y)) •
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y)

theorem rawCLM_swap_chart (form : Coefficients X) {x x' y : X}
    (hxy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source)
    (hx'y : y ∈ (extChartAt 𝓘(ℂ, ℂ) x').source) :
    rawCLM form x y = rawCLM form x' y := by
  
  set z : ℂ := (extChartAt 𝓘(ℂ, ℂ) x) y with hz_def
  
  have hz_tgt : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target :=
    (extChartAt 𝓘(ℂ, ℂ) x).map_source hxy
  
  have hsymm : (extChartAt 𝓘(ℂ, ℂ) x).symm z = y :=
    (extChartAt 𝓘(ℂ, ℂ) x).left_inv hxy
  
  have hcoc : form.coeff x z =
      form.coeff x' ((extChartAt 𝓘(ℂ, ℂ) x') ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1) :=
    form.cocycle x x' z hz_tgt (by rw [hsymm]; exact hx'y)
  
  rw [hsymm] at hcoc
  
  have hmdiff_x : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
  have hmdiff_x' : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x') y := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
  
  have hmdiff_symm : MDifferentiableWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ))) z :=
    mdifferentiableWithinAt_extChartAt_symm hz_tgt
  
  have hLocalEq : (extChartAt 𝓘(ℂ, ℂ) x') =ᶠ[𝓝 y]
      (((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ∘ (extChartAt 𝓘(ℂ, ℂ) x)) := by
    filter_upwards [extChartAt_source_mem_nhds' hxy] with w hw
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) x).left_inv hw]
  
  have hmfd_eq : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x') y =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ∘ (extChartAt 𝓘(ℂ, ℂ) x)) y := by
    exact hLocalEq.mfderiv_eq
  
  have hsymm_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z := by
    
    have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    rw [← mdifferentiableWithinAt_univ, ← hrange]
    exact hmdiff_symm
  have hTrans_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z := by
    
    have hcomp : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z := by
      have := (hsymm ▸ hmdiff_x' :
        MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x')
          ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      exact this.comp z hsymm_mdiff
    exact hcomp
  
  have hcomp_chain : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ∘ (extChartAt 𝓘(ℂ, ℂ) x)) y =
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z).comp
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) :=
    mfderiv_comp_of_eq hTrans_mdiff hmdiff_x hz_def.symm
  
  have hmfd_x'_chain : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x') y =
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z).comp
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) :=
    hmfd_eq.trans hcomp_chain
  
  unfold rawCLM
  rw [hcoc, mul_smul, hmfd_x'_chain]
  
  congr 1
  
  have hmfd_trans : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z =
      fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z :=
    mfderiv_eq_fderiv
  rw [hmfd_trans]
  
  apply ContinuousLinearMap.ext
  intro v
  
  change (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1) •
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) v =
      (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z)
        ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) v)
  
  set T := fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z with hT_def
  set w : ℂ := (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) v with hw_def
  
  have : T w = w • T 1 := by
    conv_lhs => rw [show w = w • (1 : ℂ) from (mul_one w).symm]
    rw [ContinuousLinearMap.map_smul]
  rw [this]
  
  change T 1 * w = w * T 1
  ring

noncomputable def nativeForm (form : Coefficients X) : HolomorphicForm X :=
    { toFun := fun y => rawCLM form y y
      contMDiff_toFun := by
        
        intro y₀
        
        have hSwap :
            (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (rawCLM form y y)) =ᶠ[𝓝 y₀]
            (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (rawCLM form y₀ y)) := by
          filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) y₀] with y hy
          
          have hy_y : y ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := mem_extChartAt_source y
          rw [show rawCLM form y y = rawCLM form y₀ y from
            rawCLM_swap_chart form hy_y hy]
        
        suffices h : ContMDiffAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
            (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (rawCLM form y₀ y)) y₀ from
          h.congr_of_eventuallyEq hSwap
        
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        
        have hChart : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (extChartAt 𝓘(ℂ, ℂ) y₀) y₀ :=
          contMDiffAt_extChartAt
        
        have hCoeff_analyticAt : AnalyticAt ℂ (form.coeff y₀) ((extChartAt 𝓘(ℂ, ℂ) y₀) y₀) := by
          have h_an_on : AnalyticOn ℂ (form.coeff y₀) (extChartAt 𝓘(ℂ, ℂ) y₀).target :=
            (form.analytic y₀).analyticOn
          have h_in_tgt : (extChartAt 𝓘(ℂ, ℂ) y₀) y₀ ∈ (extChartAt 𝓘(ℂ, ℂ) y₀).target :=
            mem_extChartAt_target y₀
          
          have hOpen : IsOpen (extChartAt 𝓘(ℂ, ℂ) y₀).target := by
            rw [extChartAt_target]
            simp [(chartAt ℂ y₀).open_target]
          exact h_an_on.analyticAt (hOpen.mem_nhds h_in_tgt)
        
        have hCoeff_smooth : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (form.coeff y₀)
            ((extChartAt 𝓘(ℂ, ℂ) y₀) y₀) :=
          hCoeff_analyticAt.contDiffAt.contMDiffAt
        
        have hScalar : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
            (fun y => form.coeff y₀ ((extChartAt 𝓘(ℂ, ℂ) y₀) y)) y₀ :=
          hCoeff_smooth.comp y₀ hChart
        
        have hSmul : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
            (fun y => (form.coeff y₀ ((extChartAt 𝓘(ℂ, ℂ) y₀) y)) •
              (ContinuousLinearMap.id ℂ ℂ)) y₀ :=
          hScalar.smul contMDiffAt_const
        
        apply hSmul.congr_of_eventuallyEq
        
        filter_upwards [
          ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt ℂ _ y₀))
          ] with y hy_TS_X
        
        apply ContinuousLinearMap.ext
        intro v
        simp only [ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_apply,
          Bundle.Trivial.fiberBundle_trivializationAt',
          Bundle.Trivial.continuousLinearMapAt_trivialization,
          ContinuousLinearMap.id_apply,
          smul_apply, smul_eq_mul]
        
        unfold rawCLM
        
        have hy_chart : y ∈ (chartAt ℂ y₀).source := by
          
          simpa only [TangentBundle.trivializationAt_baseSet] using hy_TS_X
        have hmfd_eq : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y₀) y =
            (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀).continuousLinearMapAt ℂ y :=
          (TangentBundle.continuousLinearMapAt_trivializationAt hy_chart).symm
        
        change form.coeff y₀ ((extChartAt 𝓘(ℂ, ℂ) y₀) y) •
            ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y₀) y)
              ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀).symmL ℂ y v)) =
          form.coeff y₀ ((extChartAt 𝓘(ℂ, ℂ) y₀) y) * v
        rw [hmfd_eq]
        
        have hroundtrip :
            (Bundle.Trivialization.continuousLinearMapAt ℂ
                (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀) y)
              ((Bundle.Trivialization.symmL ℂ
                  (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀) y) v) = v := by
          exact Bundle.Trivialization.continuousLinearMapAt_symmL
            (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀) hy_TS_X v
        calc
          form.coeff y₀ ((extChartAt 𝓘(ℂ, ℂ) y₀) y) •
              (Bundle.Trivialization.continuousLinearMapAt ℂ
                (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀) y)
                ((Bundle.Trivialization.symmL ℂ
                  (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y₀) y) v) =
              form.coeff y₀ ((extChartAt 𝓘(ℂ, ℂ) y₀) y) • v := by
                rw [hroundtrip]
          _ = form.coeff y₀ ((extChartAt 𝓘(ℂ, ℂ) y₀) y) * v := by
                simp only [smul_eq_mul]
        }

theorem nativeForm_toFun (form : Coefficients X) (x y : X)
    (hy : y ∈ (extChartAt 𝓘(ℂ) x).source) :
    (nativeForm form).toFun y = rawCLM form x y :=
  rawCLM_swap_chart form (mem_extChartAt_source y) hy


theorem nativeForm_coefficient (form : Coefficients X) (x y : X)
    (hy : y ∈ (chartAt ℂ x).source) :
    (nativeForm form).toFun y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1) =
      form.coeff x ((extChartAt 𝓘(ℂ) x) y) := by
  have hyext : y ∈ (extChartAt 𝓘(ℂ) x).source := by
    simpa only [extChartAt_source] using hy
  rw [nativeForm_toFun form x y hyext]
  unfold rawCLM
  rw [smul_apply, ← TangentBundle.continuousLinearMapAt_trivializationAt hy]
  rw [Bundle.Trivialization.continuousLinearMapAt_symmL _ hy]
  simp only [smul_eq_mul, mul_one]

end VeechDichotomy.CotangentGluing
