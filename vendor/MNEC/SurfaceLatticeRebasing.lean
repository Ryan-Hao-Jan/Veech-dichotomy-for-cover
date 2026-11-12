module

public import MNEC.SlitSurfaceCongruence
public import MNEC.CutLatticeRebasing
public import MNEC.RegularChartedSpace

@[expose] public section

/-!
# The actual slit quotient is unchanged by computed lattice rebasing

Physical projection compatibility produces proved cut maps, hence exact
seam compatibility and a genuine quotient homeomorphism. Initial/terminal
points, regular points and the two off-slit pieces are preserved. The final
primitive specialization has only integer coprimality inputs, not a supplied
surface isomorphism. Affine charts, flow and area transport remain separate.
-/

noncomputable section

namespace MNEC.SurfaceLatticeRebasing

open LatticeTorus CutTorus SlitConnectedSum RegularPoints RegularChartedSpace
open CutLatticeRebasing SlitSurfaceCongruence Set

variable {L M L₁ L₂ M₁ M₂ : Lattice}

theorem bankCompatible (e : PhysicalTorusEquiv L M) (w : Plane) :
    BankCompatible (e.cutHomeomorph w) :=
  ⟨e.cutHomeomorph_upper_project w, e.cutHomeomorph_lower_project w⟩

def offHomeomorph (e : PhysicalTorusEquiv L M) (w : Plane) : OffSlit M w ≃ₜ OffSlit L w where
  toFun p := ⟨e.torus p, fun h => p.property ((e.mem_slitSet_iff w p).mp h)⟩
  invFun p := ⟨e.symm.torus p, fun h => p.property ((e.symm.mem_slitSet_iff w p).mp h)⟩
  left_inv p := Subtype.ext (e.torus.symm_apply_apply p)
  right_inv p := Subtype.ext (e.torus.apply_symm_apply p)
  continuous_toFun := (e.torus.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.torus.symm.continuous.comp continuous_subtype_val).subtype_mk _

def surfaceHomeomorph (e₁ : PhysicalTorusEquiv L₁ M₁) (e₂ : PhysicalTorusEquiv L₂ M₂)
    (w : Plane) : Surface M₁ M₂ w ≃ₜ Surface L₁ L₂ w :=
  SlitSurfaceCongruence.surfaceHomeomorph (e₁.cutHomeomorph w) (e₂.cutHomeomorph w)
    (bankCompatible e₁ w) (bankCompatible e₂ w)

@[simp] theorem surfaceHomeomorph_left (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (p : Point M₁ w) :
    surfaceHomeomorph e₁ e₂ w (left M₁ M₂ w p) = left L₁ L₂ w (e₁.cutHomeomorph w p) := rfl

@[simp] theorem surfaceHomeomorph_right (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (p : Point M₂ w) :
    surfaceHomeomorph e₁ e₂ w (right M₁ M₂ w p) = right L₁ L₂ w (e₂.cutHomeomorph w p) := rfl

@[simp] theorem surfaceHomeomorph_leftOff (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (p : OffSlit M₁ w) :
    surfaceHomeomorph e₁ e₂ w (leftOff M₁ M₂ w p) =
      leftOff L₁ L₂ w (offHomeomorph e₁ w p) := by
  change surfaceHomeomorph e₁ e₂ w (left M₁ M₂ w (upper M₁ w p.val)) = _
  rw [surfaceHomeomorph_left, e₁.cutHomeomorph_upper]
  rfl

@[simp] theorem surfaceHomeomorph_rightOff (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (p : OffSlit M₂ w) :
    surfaceHomeomorph e₁ e₂ w (rightOff M₁ M₂ w p) =
      rightOff L₁ L₂ w (offHomeomorph e₂ w p) := by
  change surfaceHomeomorph e₁ e₂ w (right M₁ M₂ w (upper M₂ w p.val)) = _
  rw [surfaceHomeomorph_right, e₂.cutHomeomorph_upper]
  rfl

@[simp] theorem surfaceHomeomorph_initial (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) :
    surfaceHomeomorph e₁ e₂ w (initialPoint M₁ M₂ w) = initialPoint L₁ L₂ w := by
  unfold initialPoint
  rw [surfaceHomeomorph_left, e₁.cutHomeomorph_upper_project]

@[simp] theorem surfaceHomeomorph_terminal (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) :
    surfaceHomeomorph e₁ e₂ w (terminalPoint M₁ M₂ w) = terminalPoint L₁ L₂ w := by
  unfold terminalPoint
  rw [surfaceHomeomorph_left, e₁.cutHomeomorph_upper_project]

theorem mem_endpointSet_iff (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (p : Surface M₁ M₂ w) :
    surfaceHomeomorph e₁ e₂ w p ∈ endpointSet L₁ L₂ w ↔ p ∈ endpointSet M₁ M₂ w := by
  simp only [endpointSet, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((surfaceHomeomorph e₁ e₂ w).injective
        (h.trans (surfaceHomeomorph_initial e₁ e₂ w).symm))
    · exact Or.inr ((surfaceHomeomorph e₁ e₂ w).injective
        (h.trans (surfaceHomeomorph_terminal e₁ e₂ w).symm))
  · rintro (rfl | rfl)
    · exact Or.inl (surfaceHomeomorph_initial e₁ e₂ w)
    · exact Or.inr (surfaceHomeomorph_terminal e₁ e₂ w)

theorem mem_regularSet_iff (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (p : Surface M₁ M₂ w) :
    surfaceHomeomorph e₁ e₂ w p ∈ regularSet L₁ L₂ w ↔ p ∈ regularSet M₁ M₂ w :=
  not_congr (mem_endpointSet_iff e₁ e₂ w p)

def regularHomeomorph (e₁ : PhysicalTorusEquiv L₁ M₁) (e₂ : PhysicalTorusEquiv L₂ M₂)
    (w : Plane) : Regular M₁ M₂ w ≃ₜ Regular L₁ L₂ w where
  toFun p := ⟨surfaceHomeomorph e₁ e₂ w p,
    (mem_regularSet_iff e₁ e₂ w p).mpr p.property⟩
  invFun p := ⟨(surfaceHomeomorph e₁ e₂ w).symm p,
    (mem_regularSet_iff e₁ e₂ w ((surfaceHomeomorph e₁ e₂ w).symm p)).mp (by
      simpa only [Homeomorph.apply_symm_apply] using p.property)⟩
  left_inv p := Subtype.ext ((surfaceHomeomorph e₁ e₂ w).symm_apply_apply p)
  right_inv p := Subtype.ext ((surfaceHomeomorph e₁ e₂ w).apply_symm_apply p)
  continuous_toFun := ((surfaceHomeomorph e₁ e₂ w).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((surfaceHomeomorph e₁ e₂ w).symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem regularHomeomorph_value (e₁ : PhysicalTorusEquiv L₁ M₁)
    (e₂ : PhysicalTorusEquiv L₂ M₂) (w : Plane) (p : Regular M₁ M₂ w) :
    (regularHomeomorph e₁ e₂ w p).val = surfaceHomeomorph e₁ e₂ w p.val := rfl

def rebasedSurfaceHomeomorph (L₁ L₂ : Lattice) (w : Plane) (m₁ n₁ m₂ n₂ : ℤ)
    (h₁ : PrimitiveLatticeRebasing.Primitive m₁ n₁)
    (h₂ : PrimitiveLatticeRebasing.Primitive m₂ n₂) :
    Surface (PrimitiveLatticeRebasing.rebased L₁ m₁ n₁ h₁)
      (PrimitiveLatticeRebasing.rebased L₂ m₂ n₂ h₂) w ≃ₜ Surface L₁ L₂ w :=
  surfaceHomeomorph (PhysicalTorusEquiv.primitive L₁ m₁ n₁ h₁)
    (PhysicalTorusEquiv.primitive L₂ m₂ n₂ h₂) w

end MNEC.SurfaceLatticeRebasing

