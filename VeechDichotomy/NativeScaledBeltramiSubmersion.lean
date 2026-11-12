module

public import VeechDichotomy.NativeScaledBeltramiFamily

/-! The scalar-extended analytic family's actual parameter projection
is a submersion everywhere, by the product derivative and the constructed
unit-disk submersion. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeScaledBeltramiSubmersion

open MNEC.NativeAbelianDifferential NativeScaledBeltramiFamily
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem projection_surjective_derivative (q : Differential X) (p : Total q) :
    Function.Surjective (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, ℂ × ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) (projection q) p) := by
  have hi : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (id : NonzeroComplexParameter.Parameter → NonzeroComplexParameter.Parameter) p.1 :=
    mdifferentiableAt_id
  have hμ : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ) (NativeBeltramiTotalSpace.projection q) p.2 :=
    (NativeBeltramiTotalSpace.projection_holomorphic q).mdifferentiableAt (by decide)
  change Function.Surjective (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, ℂ × ℂ)) (𝓘(ℂ).prod 𝓘(ℂ))
    (Prod.map id (NativeBeltramiTotalSpace.projection q)) p)
  rw [mfderiv_prodMap hi hμ, mfderiv_id]
  intro v
  obtain ⟨w, hw⟩ := NativeBeltramiTotalSpace.projection_surjective_derivative q p.2 v.2
  exact ⟨(v.1, w), Prod.ext rfl hw⟩

end VeechDichotomy.NativeScaledBeltramiSubmersion
