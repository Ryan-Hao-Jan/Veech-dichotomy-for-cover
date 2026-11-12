module

public import VeechDichotomy.ChartPuncturePush
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith

/-! Constructed puncture disks with disjoint compact supports, avoiding
a specified basepoint. All chart, radius, and avoidance conditions used
by the radial homotopies are proved from finite Hausdorff separation. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.PunctureDisks

open Set Filter Topology Metric ChartPuncturePush

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

theorem exists_disk {S : Set X} (hS : S.Finite) {a : X} (haS : a ∈ S)
    {o : X} (ho : o ∉ S) {U : Set X} (hU : IsOpen U) (haU : a ∈ U) :
    ∃ D : Disk S, D.center = a ∧ 0 < D.radius ∧ D.support ⊆ U ∧ o ∉ D.support := by
  let A : Set X := (S \ {a}) ∪ {o}
  have hAfin : A.Finite := hS.sdiff.union (finite_singleton o)
  have haA : a ∉ A := by
    rintro (h | h)
    · exact h.2 rfl
    · exact ho (h ▸ haS)
  let V := U ∩ Aᶜ
  have hV : IsOpen V := hU.inter hAfin.isClosed.isOpen_compl
  have haV : a ∈ V := ⟨haU, haA⟩
  let c := chartAt ℂ a
  let e := c.transHomeomorph (Homeomorph.addRight (-(c a)))
  have ha : a ∈ e.source := mem_chart_source ℂ a
  have hea : e a = 0 := by
    change c a + -(c a) = 0
    exact add_neg_cancel _
  have h0T : (0 : ℂ) ∈ e.target := by rw [← hea]; exact e.map_source ha
  have hinv : e.symm 0 = a := by rw [← hea]; exact e.left_inv ha
  have hi : Tendsto e.symm (𝓝 (0 : ℂ)) (𝓝 a) := by
    simpa only [hea, hinv] using (e.symm.continuousAt (e.map_source ha)).tendsto
  have hnear : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (0 : ℂ) :=
    inter_mem (e.open_target.mem_nhds h0T) (hi (hV.mem_nhds haV))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : closedBall (0 : ℂ) r ⊆ e.target ∩ e.symm ⁻¹' V :=
    (closedBall_subset_ball (half_lt_self hR)).trans hball
  let D : Disk S :=
    { center := a
      center_mem := haS
      chart := e
      center_source := ha
      chart_center := hea
      radius := r
      radius_nonneg := hr.le
      closedBall_target := fun _ hz => (hclosed hz).1
      avoids := by
        intro z hz hz0 hzS
        have hwV : e.symm z ∈ V := (hclosed hz).2
        have hwa : e.symm z = a := by
          by_contra hne
          exact hwV.2 (Or.inl ⟨hzS, hne⟩)
        have heq := congrArg e hwa
        rw [e.right_inv (hclosed hz).1, hea] at heq
        exact hz0 heq }
  refine ⟨D, rfl, hr, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hclosed hz).2.1
  · rintro ⟨z, hz, hzo⟩
    exact (hclosed hz).2.2 (Or.inr hzo)

theorem exists_disjoint_family {S : Set X} (hS : S.Finite) {o : X} (ho : o ∉ S) :
    ∃ D : S → Disk S,
      (∀ a, (D a).center = a.val ∧ 0 < (D a).radius ∧ o ∉ (D a).support) ∧
      Pairwise (fun a b => Disjoint (D a).support (D b).support) := by
  classical
  obtain ⟨U, hU, hdisj⟩ := hS.t2_separation
  choose D hcenter hr hsub hoD using (fun a : S => exists_disk hS a.property ho (hU a.val).2 (hU a.val).1)
  refine ⟨D, fun a => ⟨hcenter a, hr a, hoD a⟩, ?_⟩
  intro a b hab
  exact (hdisj a.property b.property (fun h => hab (Subtype.ext h))).mono (hsub a) (hsub b)

end VeechDichotomy.PunctureDisks
