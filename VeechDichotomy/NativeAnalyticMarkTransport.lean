module

public import VeechDichotomy.AnalyticTransportCompositions
public import VeechDichotomy.NativeUniformMarkTransport

/-! Constructed native transport data retaining its actual disjoint disks
and displacement formulas. It gives the previous genuine marked-cover
families in explicit complex-vector parameters, with no new analytic
existence assumption. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.NativeAnalyticMarkTransport

open MNEC.NativeAbelianDifferential Set Filter Metric Topology PointTransportDisk
open LocalTranslationPlane DisjointPointTransport NativeConfigurationTransport
open ComplexDisplacementParameters NativeLocalCoverFamily PointTransportUniform
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] {m : ℕ}

structure Data (b : Fin m → X) where
  injective : Function.Injective b
  disks : Fin m → Disk (X := X)
  centers : ∀ i, (disks i).center = b i
  holomorphic : ∀ i, (disks i).chart.MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
  disjoint : Pairwise (fun i j => Disjoint (disks i).support (disks j).support)
  combined : (Fin m → Parameter) → X ≃ₜ X
  continuous_forward : Continuous (fun p : (Fin m → Parameter) × X => combined p.1 p.2)
  continuous_inverse : Continuous (fun p : (Fin m → Parameter) × X => (combined p.1).symm p.2)
  restriction : ∀ i δ x, x ∈ (disks i).support → combined δ x = (disks i).transport (δ i) x
  fixed : ∀ δ x, (∀ i, x ∉ (disks i).support) → combined δ x = x

section Construction
variable [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

theorem nonempty_data (q : Differential X) (b : Fin m → X) (hb : Function.Injective b) : Nonempty (Data b) := by
  obtain ⟨D, hD, hdisj⟩ := NativeBranchPointTransport.exists_disjoint_disks q b hb
  obtain ⟨F, hF, hInv, hown, hfixed⟩ := exists_all D hdisj
  exact ⟨⟨hb, D, fun i => (hD i).1, fun i => (hD i).2, hdisj, F, hF, hInv, hown, hfixed⟩⟩

def chosenData (q : Differential X) (b : Fin m → X) (hb : Function.Injective b) : Data b :=
  Classical.choice (nonempty_data q b hb)

end Construction

namespace Data

variable {b : Fin m → X} (A : Data b)

theorem reference_mem_neighborhood : b ∈ neighborhood A.disks := by
  intro i
  rw [← A.centers i]
  exact ⟨(A.disks i).center_source, by rw [(A.disks i).chart_center]; norm_num⟩

theorem moves (u : neighborhood A.disks) (i : Fin m) : A.combined (parameters A.disks u) (b i) = u.val i := by
  have h := A.restriction i (parameters A.disks u) (A.disks i).center (center_mem_support (A.disks i))
  rw [(A.disks i).transport_center, A.centers i] at h
  exact h.trans ((A.disks i).chart.left_inv (u.property i).1)

theorem distinct : neighborhood A.disks ⊆ configuration m X := by
  intro u hu i j hij
  apply A.injective
  apply (A.combined (parameters A.disks ⟨u, hu⟩)).injective
  rw [A.moves ⟨u, hu⟩ i, A.moves ⟨u, hu⟩ j]
  exact hij

theorem identity (u : neighborhood A.disks) (hu : u.val = b) :
    A.combined (parameters A.disks u) = Homeomorph.refl X := by
  have hp : parameters A.disks u = fun _ => zeroParameter := by
    funext i
    apply Subtype.ext
    change (A.disks i).chart (u.val i) = 0
    rw [hu, ← A.centers i, (A.disks i).chart_center]
  rw [hp]
  exact NativeBranchPointTransport.identity_at_zero A.disks A.combined A.restriction A.fixed

def marks : MarkTransport b where
  neighborhood := neighborhood A.disks
  open_neighborhood := neighborhood_open A.disks
  contains := A.reference_mem_neighborhood
  distinct := A.distinct
  transport u := A.combined (parameters A.disks u)
  continuous_transport := A.continuous_forward.comp
    (((parameters_continuous A.disks).comp continuous_fst).prodMk continuous_snd)
  continuous_inverse := A.continuous_inverse.comp
    (((parameters_continuous A.disks).comp continuous_fst).prodMk continuous_snd)
  identity := A.identity
  moves := A.moves
  holomorphic_near := by
    intro u i
    have h := NativeBranchPointTransport.holomorphic_near A.disks A.holomorphic A.combined A.restriction
      (parameters A.disks u) i
    simpa only [A.centers i] using h
  inverse_holomorphic_near := by
    intro u i
    have h := NativeBranchPointTransport.inverse_holomorphic_near A.disks A.holomorphic A.combined A.restriction
      (parameters A.disks u) i
    have heq : (A.disks i).chart.symm ((parameters A.disks u i).val) = u.val i :=
      (A.disks i).chart.left_inv (u.property i).1
    rwa [heq] at h
  isotopy := fun u => PointTransportIsotopy.exists_isotopy A.combined A.continuous_forward A.continuous_inverse
    (NativeBranchPointTransport.identity_at_zero A.disks A.combined A.restriction A.fixed) (parameters A.disks u)

def uniform : NativeUniformMarkTransport.Transport b where
  marks := A.marks
  region i := innerDisk (A.disks i)
  region_open i := innerDisk_open (A.disks i)
  region_contains i := by rw [← A.centers i]; exact center_mem_innerDisk (A.disks i)
  holomorphic u i _ hx := DisjointPointTransportUniform.holomorphic_at A.disks A.holomorphic A.combined
    A.restriction (parameters A.disks u) i hx
  inverse_holomorphic u i _ hx := DisjointPointTransportUniform.inverse_holomorphic_at A.disks A.holomorphic A.combined
    A.restriction (parameters A.disks u) i hx

def tuple (a : Parameters m) : A.marks.neighborhood :=
  ConfigurationCoordinateChart.target A.disks (productHomeomorph m a)

theorem tuple_coordinate (a : Parameters m) (i : Fin m) :
    (A.disks i).chart ((A.tuple a).val i) = a.val i :=
  (A.disks i).chart.right_inv ((A.disks i).parameter_target (productHomeomorph m a i))

theorem transport_in_coordinates (a : Parameters m) :
    A.marks.transport (A.tuple a) = AnalyticTransportCoordinates.transport A.combined a := by
  apply congrArg A.combined
  funext i
  apply Subtype.ext
  exact A.tuple_coordinate a i

theorem ambient_in_coordinates (a : Parameters m) :
    AnalyticTransportCoordinates.ambientTransport A.combined a.val = A.marks.transport (A.tuple a) := by
  rw [transport_in_coordinates, AnalyticTransportCoordinates.ambientTransport]
  have h := (ComplexDisplacementParameters.chart m).left_inv (show a ∈ (ComplexDisplacementParameters.chart m).source by
    rw [chart_source]; exact mem_univ a)
  exact congrArg (AnalyticTransportCoordinates.transport A.combined) h

end Data
end VeechDichotomy.NativeAnalyticMarkTransport
