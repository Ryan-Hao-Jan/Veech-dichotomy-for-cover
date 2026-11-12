module

public import MNEC.SlitCollars
public import MNEC.LatticeTorusMeasure
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section

/-!
# Constructed physical planar charts off the connected-sum seam

The charts restrict the proved lattice quotient charts to the slit
complement and extend along the proved open embeddings into the actual
surface. Their domains, values, coverage, and local translation transitions
are derived from these constructions. No atlas or chart existence is assumed.
-/

noncomputable section

namespace MNEC.OffSlitCharts

open LatticeTorus SlitConnectedSum SlitCollars OffSlitEmbeddings Set Topology
open scoped Classical Topology

def offOpen (L : Lattice) (w : Plane) : TopologicalSpace.Opens Torus :=
  ⟨(L.slitSet w)ᶜ, (L.slitSet_closed w).isOpen_compl⟩

theorem offOpen_nonempty (L : Lattice) (w : Plane) : Nonempty (offOpen L w) := by
  have hmass : L.area (L.slitSet w)ᶜ ≠ 0 := by
    rw [L.area_off_slit]
    exact (ENNReal.ofReal_pos.mpr L.covolume_pos).ne'
  obtain ⟨p, hp⟩ := MeasureTheory.nonempty_of_measure_ne_zero hmass
  exact ⟨⟨p, hp⟩⟩

def offTorusChart (L : Lattice) (w a : Plane) :
    OpenPartialHomeomorph (OffSlit L w) Plane :=
  (torusChart L a).symm.subtypeRestr (s := offOpen L w) (offOpen_nonempty L w)

theorem offTorusChart_apply (L : Lattice) (w a : Plane) (p : OffSlit L w) :
    offTorusChart L w a p = (torusChart L a).symm p := rfl

theorem offTorusChart_source (L : Lattice) (w a : Plane) :
    (offTorusChart L w a).source = Subtype.val ⁻¹' (torusChart L a).target := by
  simp only [offTorusChart, OpenPartialHomeomorph.subtypeRestr_source,
    OpenPartialHomeomorph.symm_source]
  rfl

theorem offTorusChart_target (L : Lattice) (w a : Plane) :
    (offTorusChart L w a).target =
      (torusChart L a).source ∩ L.project ⁻¹' (L.slitSet w)ᶜ := by
  simp only [offTorusChart, OpenPartialHomeomorph.subtypeRestr_def,
    OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
    OpenPartialHomeomorph.symm_symm,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  rfl

theorem offTorusChart_symm_val (L : Lattice) (w a p : Plane)
    (hp : p ∈ (offTorusChart L w a).target) :
    ((offTorusChart L w a).symm p).val = L.project p := by
  exact (torusChart L a).symm.subtypeRestr_symm_apply (offOpen_nonempty L w) hp

section Lift

variable {Y : Type*} [TopologicalSpace Y]

def physicalChart (L : Lattice) (w a : Plane) (f : OffSlit L w → Y)
    (hf : IsOpenEmbedding f) : OpenPartialHomeomorph Plane Y :=
  ((offTorusChart L w a).lift_openEmbedding hf).symm

theorem physicalChart_source (L : Lattice) (w a : Plane) (f : OffSlit L w → Y)
    (hf : IsOpenEmbedding f) :
    (physicalChart L w a f hf).source =
      (torusChart L a).source ∩ L.project ⁻¹' (L.slitSet w)ᶜ :=
  offTorusChart_target L w a

theorem physicalChart_apply (L : Lattice) (w a p : Plane) (f : OffSlit L w → Y)
    (hf : IsOpenEmbedding f) (hp : p ∈ (physicalChart L w a f hf).source) :
    physicalChart L w a f hf p =
      f ⟨L.project p, ((physicalChart_source L w a f hf) ▸ hp).2⟩ := by
  change f ((offTorusChart L w a).symm p) = _
  congr 1
  exact Subtype.ext (offTorusChart_symm_val L w a p hp)

theorem physicalChart_cover (L : Lattice) (w : Plane) (f : OffSlit L w → Y)
    (hf : IsOpenEmbedding f) (p : OffSlit L w) :
    ∃ a : Plane, f p ∈ (physicalChart L w a f hf).target := by
  obtain ⟨x, hx⟩ := L.project_surjective p.val
  let a := chartOrigin L x
  have htarget : p.val ∈ (torusChart L a).target := by
    rw [← hx]
    exact (torusChart L a).map_source (mem_center_chart L x)
  have hp : p ∈ (offTorusChart L w a).source := by
    rw [offTorusChart_source]
    exact htarget
  refine ⟨a, ?_⟩
  change f p ∈ f '' (offTorusChart L w a).source
  exact ⟨p, hp, rfl⟩

theorem physicalChart_projection_eq (L : Lattice) (w a b p q : Plane)
    (f : OffSlit L w → Y) (hf : IsOpenEmbedding f)
    (hp : p ∈ (physicalChart L w a f hf).source)
    (hq : q ∈ (physicalChart L w b f hf).source)
    (heq : physicalChart L w a f hf p = physicalChart L w b f hf q) :
    L.project p = L.project q := by
  rw [physicalChart_apply L w a p f hf hp, physicalChart_apply L w b q f hf hq] at heq
  exact congrArg Subtype.val (hf.injective heq)

/-- On chart overlaps, equal surface points differ by an actual lattice
period in the physical plane. -/
theorem physicalChart_period_difference (L : Lattice) (w a b p q : Plane)
    (f : OffSlit L w → Y) (hf : IsOpenEmbedding f)
    (hp : p ∈ (physicalChart L w a f hf).source)
    (hq : q ∈ (physicalChart L w b f hf).source)
    (heq : physicalChart L w a f hf p = physicalChart L w b f hf q) :
    ∃ z : ℤ × ℤ, p - q = L.period z :=
  (L.project_eq_iff p q).mp (physicalChart_projection_eq L w a b p q f hf hp hq heq)

/-- Every transition is a fixed lattice-period translation on a
neighborhood of each point of its overlap domain. -/
theorem physicalChart_transition_locally_translation (L : Lattice) (w a b : Plane)
    (f : OffSlit L w → Y) (hf : IsOpenEmbedding f) (p : Plane)
    (hp : p ∈ ((physicalChart L w a f hf).trans
      (physicalChart L w b f hf).symm).source) :
    ∃ z : ℤ × ℤ, ∀ᶠ y in 𝓝 p,
      ((physicalChart L w a f hf).trans (physicalChart L w b f hf).symm) y =
        y + L.period z := by
  let e := physicalChart L w a f hf
  let d := physicalChart L w b f hf
  let F := e.trans d.symm
  have hpA : p ∈ e.source := hp.1
  have hpB : e p ∈ d.target := hp.2
  have hqB : F p ∈ d.source := d.map_target hpB
  have heq : e p = d (F p) := (d.right_inv hpB).symm
  have hprojection : L.project (F p) = L.project p :=
    (physicalChart_projection_eq L w a b p (F p) f hf hpA hqB heq).symm
  obtain ⟨z, hz⟩ := (L.project_eq_iff (F p) p).mp hprojection
  have htranslate : F p = p + L.period z := by
    have h := sub_eq_iff_eq_add.mp hz
    simpa only [add_comm] using h
  have hperiod : L.project (L.period z) = 0 :=
    (L.project_eq_zero_iff _).mpr ⟨z, rfl⟩
  let U := F.source ∩ (fun y : Plane => y + L.period z) ⁻¹' d.source
  have hU : IsOpen U := F.open_source.inter
    (d.open_source.preimage (continuous_id.add continuous_const))
  have hpU : p ∈ U := by
    refine ⟨hp, ?_⟩
    change p + L.period z ∈ d.source
    rw [← htranslate]
    exact hqB
  refine ⟨z, ?_⟩
  filter_upwards [hU.mem_nhds hpU] with y hy
  have hyA : y ∈ e.source := hy.1.1
  have hyB : e y ∈ d.target := hy.1.2
  have hFy : F y ∈ d.source := d.map_target hyB
  have heqy : e y = d (F y) := (d.right_inv hyB).symm
  have hproj : L.project (F y) = L.project y :=
    (physicalChart_projection_eq L w a b y (F y) f hf hyA hFy heqy).symm
  have hFy' : F y ∈ (torusChart L b).source :=
    ((physicalChart_source L w b f hf) ▸ hFy).1
  have htrans' : y + L.period z ∈ (torusChart L b).source :=
    ((physicalChart_source L w b f hf) ▸ hy.2).1
  apply projection_injOn_chart L b hFy' htrans'
  rw [L.project_add, hperiod, add_zero]
  exact hproj

end Lift

def leftChart (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) (a : Plane) :
    OpenPartialHomeomorph Plane (Surface L₁ L₂ w) :=
  physicalChart L₁ w a (leftOff L₁ L₂ w) (isOpenEmbedding_leftOff L₁ L₂ w hw)

def rightChart (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) (a : Plane) :
    OpenPartialHomeomorph Plane (Surface L₁ L₂ w) :=
  physicalChart L₂ w a (rightOff L₁ L₂ w) (isOpenEmbedding_rightOff L₁ L₂ w hw)

theorem leftChart_source (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) (a : Plane) :
    (leftChart L₁ L₂ w hw a).source =
      (torusChart L₁ a).source ∩ L₁.project ⁻¹' (L₁.slitSet w)ᶜ :=
  physicalChart_source _ _ _ _ _

theorem rightChart_source (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) (a : Plane) :
    (rightChart L₁ L₂ w hw a).source =
      (torusChart L₂ a).source ∩ L₂.project ⁻¹' (L₂.slitSet w)ᶜ :=
  physicalChart_source _ _ _ _ _

theorem leftChart_apply (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) (a p : Plane)
    (hp : p ∈ (leftChart L₁ L₂ w hw a).source) :
    leftChart L₁ L₂ w hw a p =
      left L₁ L₂ w (CutTorus.upper L₁ w (L₁.project p)) := by
  exact physicalChart_apply L₁ w a p _ _ hp

theorem rightChart_apply (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0) (a p : Plane)
    (hp : p ∈ (rightChart L₁ L₂ w hw a).source) :
    rightChart L₁ L₂ w hw a p =
      right L₁ L₂ w (CutTorus.upper L₂ w (L₂.project p)) := by
  exact physicalChart_apply L₂ w a p _ _ hp

theorem leftChart_cover (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0)
    (p : OffSlit L₁ w) : ∃ a, leftOff L₁ L₂ w p ∈ (leftChart L₁ L₂ w hw a).target :=
  physicalChart_cover L₁ w _ _ p

theorem rightChart_cover (L₁ L₂ : Lattice) (w : Plane) (hw : w ≠ 0)
    (p : OffSlit L₂ w) : ∃ a, rightOff L₁ L₂ w p ∈ (rightChart L₁ L₂ w hw a).target :=
  physicalChart_cover L₂ w _ _ p

end MNEC.OffSlitCharts
