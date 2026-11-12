module

public import VeechDichotomy.UniformBeltramiTransport
public import VeechDichotomy.DisjointHomeomorphFamilies
public import Mathlib.Tactic.Choose

/-! Uniform disjoint transport disks at a finite tuple of marked points.
A single open neighborhood of the deformation parameter works for every
mark, including when the tuple is empty or a mark is a differential zero. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiMarkData

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {m : ℕ}

structure Data (q : Differential X) (b : Fin m → X) (μ₀ : Parameter) where
  injective : Function.Injective b
  region : Fin m → Set X
  region_open : ∀ i, IsOpen (region i)
  contains : ∀ i, b i ∈ region i
  disjoint : Pairwise (fun i j => Disjoint (region i) (region j))
  disks : ∀ i, UniformBeltramiDiskData.Data q (b i) μ₀ (region i)

theorem nonempty_data (q : Differential X) (b : Fin m → X) (μ₀ : Parameter)
    (hb : Function.Injective b) : Nonempty (Data q b μ₀) := by
  classical
  obtain ⟨U, hU, hsep⟩ := (finite_range b).t2_separation
  let D := fun i : Fin m => UniformBeltramiDiskData.chosenData q (b i) μ₀ (hU (b i)).2 (hU (b i)).1
  refine ⟨⟨hb, fun i => U (b i), fun i => (hU (b i)).2,
    fun i => (hU (b i)).1, ?_, D⟩⟩
  intro i j hij
  exact hsep (mem_range_self i) (mem_range_self j) (fun h => hij (hb h))

def chosenData (q : Differential X) (b : Fin m → X) (μ₀ : Parameter)
    (hb : Function.Injective b) : Data q b μ₀ :=
  Classical.choice (nonempty_data q b μ₀ hb)

namespace Data

variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} (A : Data q b μ₀)

def baseNeighborhood : Set Parameter := {μ | ∀ i, dist μ.val μ₀.val < (A.disks i).epsilon}

theorem baseNeighborhood_open : IsOpen A.baseNeighborhood := by
  have heq : A.baseNeighborhood = ⋂ i : Fin m, {μ : Parameter | dist μ.val μ₀.val < (A.disks i).epsilon} := by
    ext μ
    simp only [baseNeighborhood, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_lt
    (continuous_subtype_val.dist continuous_const) continuous_const

theorem reference_mem : μ₀ ∈ A.baseNeighborhood := by
  intro i
  simpa only [dist_self] using (A.disks i).epsilon_pos

abbrev Base := A.baseNeighborhood

def localBase (μ : A.Base) (i : Fin m) : UniformBeltramiDisks.Near (A.disks i) :=
  ⟨μ.val, μ.property i⟩

theorem continuous_localBase (i : Fin m) : Continuous (fun μ : A.Base => A.localBase μ i) :=
  continuous_subtype_val.subtype_mk _

abbrev Parameters := A.Base × (Fin m → LocalTranslationPlane.Parameter)

def localParameter (p : A.Parameters) (i : Fin m) : BeltramiPlaneTransport.Parameters (A.disks i) :=
  (A.localBase p.1 i, p.2 i)

theorem continuous_localParameter (i : Fin m) : Continuous (fun p : A.Parameters => A.localParameter p i) :=
  ((A.continuous_localBase i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)

def support (i : Fin m) : Set X := UniformBeltramiTransport.support (A.disks i)

theorem support_compact (i : Fin m) : IsCompact (A.support i) :=
  UniformBeltramiTransport.support_compact (A.disks i)

theorem support_subset (i : Fin m) : A.support i ⊆ A.region i := (A.disks i).old_support

theorem support_disjoint : Pairwise (fun i j => Disjoint (A.support i) (A.support j)) :=
  fun i j hij => (A.disjoint hij).mono (A.support_subset i) (A.support_subset j)

def single (i : Fin m) (p : A.Parameters) : X ≃ₜ X :=
  UniformBeltramiTransport.oldTransport (A.disks i) (A.localParameter p i)

theorem continuous_single (i : Fin m) : Continuous (fun p : A.Parameters × X => A.single i p.1 p.2) :=
  Continuous.comp (f := fun p : A.Parameters × X => (A.localParameter p.1 i, p.2))
    (g := fun p : BeltramiPlaneTransport.Parameters (A.disks i) × X =>
      UniformBeltramiTransport.oldTransport (A.disks i) p.1 p.2)
    (UniformBeltramiTransport.continuous_oldTransport (A.disks i))
    (((A.continuous_localParameter i).comp continuous_fst).prodMk continuous_snd)

theorem continuous_single_inverse (i : Fin m) : Continuous (fun p : A.Parameters × X => (A.single i p.1).symm p.2) :=
  Continuous.comp (f := fun p : A.Parameters × X => (A.localParameter p.1 i, p.2))
    (g := fun p : BeltramiPlaneTransport.Parameters (A.disks i) × X =>
      (UniformBeltramiTransport.oldTransport (A.disks i) p.1).symm p.2)
    (UniformBeltramiTransport.continuous_oldInverse (A.disks i))
    (((A.continuous_localParameter i).comp continuous_fst).prodMk continuous_snd)

theorem single_fixed (i : Fin m) (p : A.Parameters) {x : X} (hx : x ∉ A.support i) : A.single i p x = x :=
  UniformBeltramiTransport.oldTransport_fixed (A.disks i) (A.localParameter p i) hx

theorem center_mem_support (i : Fin m) : b i ∈ A.support i := by
  refine ⟨0, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_self] using (A.disks i).oldRadius_pos.le
  · rw [← (NativePowerCharts.chosen q (b i)).center_zero]
    exact (NativePowerCharts.chosen q (b i)).chart.left_inv (NativePowerCharts.chosen q (b i)).center

end Data
end VeechDichotomy.UniformBeltramiMarkData
