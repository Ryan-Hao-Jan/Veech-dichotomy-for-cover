module

public import VeechDichotomy.PunctureDisks

/-! Finite composition of the constructed local radial homotopies.
Disjoint compact supports ensure that pushing out one puncture disk
preserves avoidance of all the others and fixes the chosen basepoint.
-/

@[expose] public section
noncomputable section

namespace VeechDichotomy.FinitePunctureHomotopy

open Set Topology Metric unitInterval ChartPuncturePush FinitePunctureNeighborhoods

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] {S : Set X}

def inner (D : Disk S) : Set X := D.chart.symm '' ball 0 D.radius

theorem inner_subset_support (D : Disk S) : inner D ⊆ D.support :=
  image_mono ball_subset_closedBall

theorem inner_open (D : Disk S) : IsOpen (inner D) :=
  D.chart.symm.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans D.closedBall_target)

theorem center_mem_inner (D : Disk S) (hr : 0 < D.radius) : D.center ∈ inner D := by
  refine ⟨0, mem_ball_self hr, ?_⟩
  rw [← D.chart_center]
  exact D.chart.left_inv D.center_source

theorem push_mem_support (D : Disk S) (t : I) (x : outside S) (hx : x.val ∈ D.support) :
    (D.push t x).val ∈ D.support := by
  have hxsource := D.support_subset_source hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hzT := D.closedBall_target hz
  have hcoord : D.chart x.val = z := by rw [← hzx, D.chart.right_inv hzT]
  have hnorm : ‖D.chart x.val‖ ≤ D.radius := by
    rw [hcoord]
    simpa only [mem_closedBall, dist_zero_right] using hz
  have hpush := RadialPuncturePush.norm_push_le D.radius_nonneg le_rfl t
    (⟨D.chart x.val, D.coordinate_ne_zero x hxsource⟩ : RadialPuncturePush.Punctured) hnorm
  change ‖RadialPuncturePush.formula D.radius t (D.chart x.val)‖ ≤ D.radius at hpush
  refine ⟨RadialPuncturePush.formula D.radius t (D.chart x.val), ?_, ?_⟩
  · simpa only [mem_closedBall, dist_zero_right] using hpush
  · change D.chart.symm (RadialPuncturePush.formula D.radius t (D.chart x.val)) = D.value t x
    rw [Disk.value, ite_eq_left hxsource]

theorem push_preserves_other_inner (D E : Disk S) (hDE : Disjoint D.support E.support)
    (t : I) (x : outside S) (hx : x.val ∉ inner E) : (D.push t x).val ∉ inner E := by
  by_cases hxD : x.val ∈ D.support
  · intro hinner
    exact disjoint_left.mp hDE (push_mem_support D t x hxD) (inner_subset_support E hinner)
  · rw [D.push_fixed_of_not_support t x hxD]
    exact hx

variable [T2Space X]

theorem exists_push {ι : Type*} (D : ι → Disk S)
    (hdisj : Pairwise (fun a b => Disjoint (D a).support (D b).support))
    (o : outside S) (ho : ∀ a, o.val ∉ (D a).support) (T : Finset ι) :
    ∃ f : C(outside S, outside S), ∃ H : (ContinuousMap.id (outside S)).Homotopy f,
      (∀ t, H (t, o) = o) ∧ ∀ a ∈ T, ∀ x : outside S, (f x).val ∉ inner (D a) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨ContinuousMap.id _, ContinuousMap.Homotopy.refl _, fun _ => rfl, ?_⟩
    intro a ha
    simp at ha
  | @insert a T haT ih =>
    obtain ⟨f, H, hHo, havoid⟩ := ih
    let g : C(outside S, outside S) := (D a).endpoint.comp f
    let J : (ContinuousMap.id (outside S)).Homotopy g :=
      { toContinuousMap := ⟨fun p => (D a).push p.1 (H p),
          (D a).continuous_push.comp (continuous_fst.prodMk H.continuous)⟩
        map_zero_left := by
          intro x
          change (D a).push 0 (H (0, x)) = x
          rw [H.apply_zero, (D a).push_zero]
          rfl
        map_one_left := by
          intro x
          change (D a).push 1 (H (1, x)) = (D a).push 1 (f x)
          rw [H.apply_one] }
    refine ⟨g, J, ?_, ?_⟩
    · intro t
      change (D a).push t (H (t, o)) = o
      rw [hHo t]
      exact (D a).push_fixed_of_not_support t o (ho a)
    · intro b hb x
      change ((D a).push 1 (f x)).val ∉ inner (D b)
      rcases Finset.mem_insert.mp hb with hba | hb
      · subst b
        exact (D a).endpoint_outside_inner (f x)
      · have hab : a ≠ b := by
          intro h
          subst b
          exact haT hb
        exact push_preserves_other_inner (D a) (D b) (hdisj hab) 1 (f x) (havoid b hb x)

end VeechDichotomy.FinitePunctureHomotopy
