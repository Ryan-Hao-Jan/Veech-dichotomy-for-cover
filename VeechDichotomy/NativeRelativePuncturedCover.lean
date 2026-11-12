module

public import VeechDichotomy.NativePuncturedCover
public import VeechDichotomy.CoverMonodromyClassification

/-! A genuine cover over the complement of any finite marked set
containing its branch values. This provides a common base for comparing
different native covers by actual monodromy. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeRelativePuncturedCover

open MNEC.NativeAbelianDifferential NativeTranslationCover Set Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {ωX : Differential X} {ωY : Differential Y}

def base (B : Set X) : Set X := Bᶜ

def source (π : Cover ωX ωY) (B : Set X) : Set Y := π.map ⁻¹' base B

def map (π : Cover ωX ωY) (B : Set X) : source π B → base B := (base B).restrictPreimage π.map

theorem isCoveringMap (π : Cover ωX ωY) {B : Set X} (hB : branchValues π ⊆ B) :
    IsCoveringMap (map π B) := by
  apply IsCoveringMapOn.isCoveringMap_restrictPreimage
  exact (NativePuncturedCover.isCoveringMapOn_base π).mono fun x hx hb => hx (hB hb)

theorem preimage_finite (π : Cover ωX ωY) {B : Set X} (hB : B.Finite) : (π.map ⁻¹' B).Finite := by
  have heq : π.map ⁻¹' B = ⋃ x ∈ B, π.map ⁻¹' {x} := by
    ext y
    simp only [mem_preimage, mem_iUnion, mem_singleton_iff]
    exact ⟨fun hy => ⟨π.map y, hy, rfl⟩, fun ⟨x, hx, hxy⟩ => hxy ▸ hx⟩
  rw [heq]
  exact hB.biUnion fun x _ => π.finite_fibers x

theorem source_open (π : Cover ωX ωY) {B : Set X} (hB : B.Finite) : IsOpen (source π B) :=
  hB.isClosed.isOpen_compl.preimage π.holomorphic.continuous

theorem source_pathConnected (π : Cover ωX ωY) {B : Set X} (hB : B.Finite) :
    PathConnectedSpace (source π B) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  let : Infinite Y := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  have hfin := preimage_finite π hB
  obtain ⟨y, hy⟩ := hfin.exists_notMem
  exact Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
    hfin ⟨y, hy⟩

theorem source_locallyPathConnected (π : Cover ωX ωY) {B : Set X} (hB : B.Finite) :
    LocallyPathConnectedSpace (source π B) := by
  let : LocallyPathConnectedSpace Y := ChartedSpace.locallyPathConnectedSpace ℂ Y
  exact (source_open π hB).locallyPathConnectedSpace

def fiberEquiv (π : Cover ωX ωY) (B : Set X) (x : base B) :
    (map π B ⁻¹' {x}) ≃ (π.map ⁻¹' {x.val}) where
  toFun y := ⟨y.val.val, congrArg Subtype.val y.property⟩
  invFun y := ⟨⟨y.val, by
    change π.map y.val ∈ Bᶜ
    rw [y.property]
    exact x.property⟩, Subtype.ext y.property⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem fiber_finite (π : Cover ωX ωY) (B : Set X) (x : base B) : Finite (map π B ⁻¹' {x}) := by
  let : Finite (π.map ⁻¹' {x.val}) := (π.finite_fibers x.val).to_subtype
  exact Finite.of_equiv _ (fiberEquiv π B x).symm

end VeechDichotomy.NativeRelativePuncturedCover
