module

public import VeechDichotomy.BeltramiPlane
public import VeechDichotomy.HomeomorphicPowerLift

/-! Simultaneous homeomorphic power lifts for ALL complex unit-disk
parameters. The forward maps and their inverses vary jointly continuously,
including at zero, with literal power identities. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiPowerLift

open BeltramiPlane Set Filter Topology

set_option backward.isDefEq.respectTransparency false

def rootHomeomorph (μ : Parameter) (k : ℕ) (hk : 0 < k) : ℂ ≃ₜ ℂ :=
  HomeomorphicPowerLift.homeomorph (BeltramiPlane.homeomorph μ) (map_zero μ.val)
    (fun _ hz => ratio_slitPlane μ hz) (fun _ hz => inverse_ratio_slitPlane μ hz) k hk

theorem rootHomeomorph_pow (μ : Parameter) {k : ℕ} (hk : 0 < k) (z : ℂ) :
    rootHomeomorph μ k hk z ^ k = BeltramiPlane.map μ.val (z ^ k) :=
  HomeomorphicPowerLift.lift_pow _ (map_zero μ.val) hk z

@[simp] theorem rootHomeomorph_zero (μ : Parameter) {k : ℕ} (hk : 0 < k) :
    rootHomeomorph μ k hk 0 = 0 := HomeomorphicPowerLift.lift_zero _ _

theorem continuous_forward {k : ℕ} (hk : 0 < k) :
    Continuous (fun p : Parameter × ℂ => rootHomeomorph p.1 k hk p.2) :=
  HomeomorphicPowerLift.continuous_family BeltramiPlane.homeomorph BeltramiPlane.continuous_forward
    (fun μ => map_zero μ.val) (fun μ _ hz => ratio_slitPlane μ hz) hk

theorem continuous_inverse {k : ℕ} (hk : 0 < k) :
    Continuous (fun p : Parameter × ℂ => (rootHomeomorph p.1 k hk).symm p.2) :=
  HomeomorphicPowerLift.continuous_family (fun μ : Parameter => (BeltramiPlane.homeomorph μ).symm)
    BeltramiPlane.continuous_inverse (fun μ => inverseMap_zero μ.val)
    (fun μ _ hz => inverse_ratio_slitPlane μ hz) hk

end VeechDichotomy.BeltramiPowerLift
