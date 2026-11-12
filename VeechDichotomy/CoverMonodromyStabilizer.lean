module

public import VeechDichotomy.CoverMonodromy

/-! The stabilizer of a sheet under actual monodromy is the image of the
covering space's fundamental group. This uses the path lift as a loop
precisely when its endpoint is its initial sheet. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.CoverMonodromyStabilizer

open Set Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (cov : IsCoveringMap p)

theorem fixed_iff_range {x : X} (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    cov.monodromyPerm x γ e = e ↔
      γ ∈ (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.property).range := by
  constructor
  · intro h
    let Γ : Path.Homotopic.Quotient e.val e.val :=
      (cov.liftPathQuotient γ.asHom e).cast rfl (congrArg Subtype.val h.symm)
    refine ⟨.of Γ, ?_⟩
    rw [FundamentalGroup.mapOfEq_apply]
    dsimp only [Γ]
    rw [Path.Homotopic.Quotient.map_cast, IsCoveringMap.map_liftPathQuotient]
    aesop
  · rintro ⟨η, rfl⟩
    change cov.monodromy (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.property η).asHom e = e
    apply cov.monodromy_eq_of_map_eq η.asHom
    aesop (add simp FundamentalGroup.mapOfEq_apply)

end VeechDichotomy.CoverMonodromyStabilizer
