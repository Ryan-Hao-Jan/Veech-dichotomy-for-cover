module

public import VeechDichotomy.BeltramiMarkedLimitRectangles
public import VeechDichotomy.BeltramiMarkedRectangleNeighborhoods
public import VeechDichotomy.NativeRegularBoxChains

/-! Finite chains of ACTUAL good persistent family rectangles. Their
overlap graph is connected on the regular limit fiber; the chain retains
the fixed family charts required by the native local mean comparison. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.BeltramiMarkedRectangleChains

open MNEC.NativeAbelianDifferential MNEC.NativeRegularTranslationAtlas
open NativeTranslationCover BeltramiPlane Set Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport BeltramiMarkedScaledFamily
open BeltramiMarkedLimitRectangles
open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {qX : Differential X} {qY : Differential Y} {m : ℕ} {b : Fin m → X} {μ₀ : Parameter}
variable (π : Cover qX qY) {A : Data qX b μ₀} (F : Family A) (hBranch : range b = branchValues π)
variable (p₀ : Base A)

def Overlap (B C : Rectangle π F hBranch p₀) : Prop := (B.regularRegion ∩ C.regularRegion).Nonempty

theorem region_nonempty (B : Rectangle π F hBranch p₀) : B.regularRegion.Nonempty := by
  obtain ⟨z, hzreg, hzW⟩ := BeltramiMarkedRectangleNeighborhoods.exists_regular_point π F hBranch
    B.slice B.not_critical B.base_regular p₀ B.width_pos B.height_pos B.target 0 0
  exact ⟨⟨z, hzreg⟩, hzW.1, ⟨hzW.2.1.1, hzW.2.2⟩⟩

theorem connected (hzero : ∀ i, p₀.2.val.2 i = 0) (B C : Rectangle π F hBranch p₀) :
    Relation.ReflTransGen (Overlap π F hBranch p₀) B C := by
  let : PreconnectedSpace (Regular (fiberForm π F hBranch p₀)) := isPreconnected_iff_preconnectedSpace.mp
    (NativeRegularBoxChains.regular_pathConnected (fiberForm π F hBranch p₀)).isConnected.isPreconnected
  let S : Set (Regular (fiberForm π F hBranch p₀)) :=
    {z | ∃ D : Rectangle π F hBranch p₀, Relation.ReflTransGen (Overlap π F hBranch p₀) B D ∧ z ∈ D.regularRegion}
  have hopen : IsOpen S := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro z ⟨D, hBD, hzD⟩
    exact ⟨D.regularRegion, fun w hw => ⟨D, hBD, hw⟩, D.regularRegion_open, hzD⟩
  have hcomp : IsOpen Sᶜ := by
    apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    obtain ⟨D, hzD⟩ := covers_regular π F hBranch p₀ hzero z
    refine ⟨D.regularRegion, ?_, D.regularRegion_open, hzD⟩
    rintro w hw ⟨T, hBT, hwT⟩
    exact hz ⟨D, Relation.ReflTransGen.tail hBT ⟨w, hwT, hw⟩, hzD⟩
  have hclosed : IsClosed S := isOpen_compl_iff.mp hcomp
  have hclopen : IsClopen S := ⟨hclosed, hopen⟩
  obtain ⟨x, hx⟩ := region_nonempty π F hBranch p₀ B
  have huniv : S = univ := hclopen.eq_univ ⟨x, B, Relation.ReflTransGen.refl, hx⟩
  obtain ⟨y, hy⟩ := region_nonempty π F hBranch p₀ C
  have hymem : y ∈ S := huniv.symm ▸ mem_univ y
  obtain ⟨D, hBD, hyD⟩ := hymem
  exact Relation.ReflTransGen.tail hBD ⟨y, hyD, hy⟩

theorem finite_relation_path {V : Type*} {r : V → V → Prop} {a b : V} (h : Relation.ReflTransGen r a b) :
    ∃ n : ℕ, ∃ f : ℕ → V, f 0 = a ∧ f n = b ∧ ∀ i < n, r (f i) (f (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, f, hf0, hfn, hstep⟩ := ih
    let g : ℕ → V := fun i => if i ≤ n then f i else c
    refine ⟨n + 1, g, ?_, ?_, ?_⟩
    · simpa only [g, ite_eq_left (Nat.zero_le n)] using hf0
    · simp only [g, ite_eq_right (by omega : ¬ n + 1 ≤ n)]
    · intro i hi
      by_cases hin : i < n
      · simpa only [g, ite_eq_left (Nat.le_of_lt hin), ite_eq_left (by omega : i + 1 ≤ n)] using hstep i hin
      · have heq : i = n := by omega
        subst i
        simpa only [g, ite_eq_left le_rfl, ite_eq_right (by omega : ¬ n + 1 ≤ n), hfn] using hbc

theorem finite_chain (hzero : ∀ i, p₀.2.val.2 i = 0) (B C : Rectangle π F hBranch p₀) :
    ∃ n : ℕ, ∃ f : ℕ → Rectangle π F hBranch p₀,
      f 0 = B ∧ f n = C ∧ ∀ i < n, Overlap π F hBranch p₀ (f i) (f (i + 1)) :=
  finite_relation_path (connected π F hBranch p₀ hzero B C)

end VeechDichotomy.BeltramiMarkedRectangleChains
