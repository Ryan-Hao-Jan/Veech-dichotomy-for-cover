module

public import VeechDichotomy.PointTransportDisk

/-! Disjoint local point transports combine into a genuine family of
whole homeomorphisms. Both directions vary jointly continuously, and on
each marked disk the family is exactly its single local transport. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.DisjointPointTransport

open Set Filter Metric Topology PointTransportDisk LocalTranslationPlane

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]

theorem support_mem_nhds (D : Disk (X := X)) {x : X} (hx : x ∈ D.chart.source)
    (hn : ‖D.chart x‖ < 2) : D.support ∈ 𝓝 x := by
  have hball : ball (0 : ℂ) 2 ∈ 𝓝 (D.chart x) := isOpen_ball.mem_nhds (by
    simpa only [mem_ball, dist_zero_right] using hn)
  have hnear : D.chart.source ∩ D.chart ⁻¹' ball 0 2 ∈ 𝓝 x :=
    inter_mem (D.chart.open_source.mem_nhds hx) (D.chart.continuousAt hx hball)
  apply mem_of_superset hnear
  intro y hy
  exact ⟨D.chart y, ball_subset_closedBall hy.2, D.chart.left_inv hy.1⟩

theorem center_mem_support (D : Disk (X := X)) : D.center ∈ D.support :=
  mem_of_mem_nhds (support_mem_nhds D D.center_source (by rw [D.chart_center]; norm_num))

theorem mapsTo_of_fixed (H : X ≃ₜ X) {S : Set X} (hfix : ∀ x ∉ S, H x = x) : MapsTo H S S := by
  intro x hx
  by_contra hnot
  have heq : H x = x := H.injective (hfix (H x) hnot)
  rw [heq] at hnot
  exact hnot hx

variable [T2Space X]

def zeroParameter : Parameter := ⟨0, by norm_num⟩

theorem transport_zero (D : Disk (X := X)) (x : X) : D.transport zeroParameter x = x := by
  by_cases hx : x ∈ D.chart.source
  · rw [D.transport_apply_of_source zeroParameter hx, homeomorph_apply, move]
    change D.chart.symm (D.chart x + cutoff (D.chart x) • (0 : ℂ)) = x
    rw [smul_zero, add_zero, D.chart.left_inv hx]
  · change ChartHomeomorphExtension.value D.chart (LocalTranslationPlane.homeomorph zeroParameter) x = x
    rw [ChartHomeomorphExtension.value, ite_eq_right hx]

theorem transport_maps_support (D : Disk (X := X)) (δ : Parameter) :
    MapsTo (D.transport δ) D.support D.support := mapsTo_of_fixed _ (fun _ hx => D.transport_fixed δ hx)

theorem inverse_maps_support (D : Disk (X := X)) (δ : Parameter) :
    MapsTo (D.transport δ).symm D.support D.support := mapsTo_of_fixed _ (fun _ hx => D.transport_inverse_fixed δ hx)

theorem exists_family {ι : Type*} (D : ι → Disk (X := X))
    (hdisj : Pairwise (fun i j => Disjoint (D i).support (D j).support)) (T : Finset ι) :
    ∃ F : (ι → Parameter) → X ≃ₜ X,
      Continuous (fun p : (ι → Parameter) × X => F p.1 p.2) ∧
      Continuous (fun p : (ι → Parameter) × X => (F p.1).symm p.2) ∧
      (∀ i ∈ T, ∀ δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x) ∧
      (∀ i ∉ T, ∀ δ x, x ∈ (D i).support → F δ x = x) ∧
      (∀ δ x, (∀ i ∈ T, x ∉ (D i).support) → F δ x = x) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => Homeomorph.refl X, continuous_snd, continuous_snd, ?_, ?_, ?_⟩
    · intro i hi
      simp at hi
    · intro i _ δ x _
      rfl
    · intro δ x _
      rfl
  | @insert a T haT ih =>
    obtain ⟨F, hF, hInv, hown, hother, hfixed⟩ := ih
    let G : (ι → Parameter) → X ≃ₜ X := fun δ => (F δ).trans ((D a).transport (δ a))
    have hδ : Continuous (fun p : (ι → Parameter) × X => p.1 a) := (continuous_apply a).comp continuous_fst
    have hG : Continuous (fun p : (ι → Parameter) × X => G p.1 p.2) :=
      (D a).continuous_transport.comp (hδ.prodMk hF)
    have hGInv : Continuous (fun p : (ι → Parameter) × X => (G p.1).symm p.2) := by
      have hstep := (D a).continuous_transport_inverse.comp (hδ.prodMk continuous_snd)
      exact hInv.comp (continuous_fst.prodMk hstep)
    refine ⟨G, hG, hGInv, ?_, ?_, ?_⟩
    · intro i hi δ x hx
      change (D a).transport (δ a) (F δ x) = (D i).transport (δ i) x
      rcases Finset.mem_insert.mp hi with hia | hi
      · subst i
        rw [hother a haT δ x hx]
      · have hai : a ≠ i := by
          intro h
          subst i
          exact haT hi
        have hnot : (D i).transport (δ i) x ∉ (D a).support := fun ha =>
          disjoint_left.mp (hdisj hai) ha (transport_maps_support (D i) (δ i) hx)
        rw [hown i hi δ x hx, (D a).transport_fixed (δ a) hnot]
    · intro i hi δ x hx
      have hiT : i ∉ T := fun hit => hi (Finset.mem_insert_of_mem hit)
      have hai : a ≠ i := by
        intro h
        subst i
        exact hi (by simp)
      have hnot : x ∉ (D a).support := fun ha => disjoint_left.mp (hdisj hai) ha hx
      change (D a).transport (δ a) (F δ x) = x
      rw [hother i hiT δ x hx, (D a).transport_fixed (δ a) hnot]
    · intro δ x hx
      have hrest : ∀ i ∈ T, x ∉ (D i).support := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      change (D a).transport (δ a) (F δ x) = x
      rw [hfixed δ x hrest]
      exact (D a).transport_fixed (δ a) (hx a (by simp))

theorem exists_all {ι : Type*} [Finite ι] (D : ι → Disk (X := X))
    (hdisj : Pairwise (fun i j => Disjoint (D i).support (D j).support)) :
    ∃ F : (ι → Parameter) → X ≃ₜ X,
      Continuous (fun p : (ι → Parameter) × X => F p.1 p.2) ∧
      Continuous (fun p : (ι → Parameter) × X => (F p.1).symm p.2) ∧
      (∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x) ∧
      (∀ δ x, (∀ i, x ∉ (D i).support) → F δ x = x) := by
  let := Fintype.ofFinite ι
  obtain ⟨F, hF, hInv, hown, _, hfixed⟩ := exists_family D hdisj Finset.univ
  exact ⟨F, hF, hInv, fun i => hown i (Finset.mem_univ i), fun δ x hx => hfixed δ x (fun i _ => hx i)⟩

theorem inverse_restriction {ι : Type*} (D : ι → Disk (X := X))
    (F : (ι → Parameter) → X ≃ₜ X)
    (hown : ∀ i δ x, x ∈ (D i).support → F δ x = (D i).transport (δ i) x)
    (δ : ι → Parameter) (i : ι) {x : X} (hx : x ∈ (D i).support) :
    (F δ).symm x = ((D i).transport (δ i)).symm x := by
  let y := ((D i).transport (δ i)).symm x
  have hy : y ∈ (D i).support := inverse_maps_support (D i) (δ i) hx
  have heq : F δ y = x := (hown i δ y hy).trans (((D i).transport (δ i)).apply_symm_apply x)
  calc
    (F δ).symm x = (F δ).symm (F δ y) := congrArg (F δ).symm heq.symm
    _ = y := (F δ).symm_apply_apply y

end VeechDichotomy.DisjointPointTransport
