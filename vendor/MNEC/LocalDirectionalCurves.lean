module

public import MNEC.RegularTranslationStructure
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Actual local straight trajectories in the regular quotient

The curves are computed in the proved physical charts. Their valid-time
sets are open, the coordinate velocity is the prescribed physical vector,
and curves from overlapping charts agree near the initial time. No global
flow, complete nonsingular domain, or area-preservation claim is assumed.
-/

noncomputable section

namespace MNEC.LocalDirectionalCurves

open LatticeTorus RegularChartedSpace RegularAtlasCoverage Filter Set
open scoped Topology

def timeDomain {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) : Set ℝ :=
  {t | regularChart hw₁ hw₂ i x + t • v ∈ (regularChart hw₁ hw₂ i).target}

def curve {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ) : Regular L₁ L₂ w :=
  (regularChart hw₁ hw₂ i).symm (regularChart hw₁ hw₂ i x + t • v)

theorem timeDomain_open {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) :
    IsOpen (timeDomain hw₁ hw₂ i v x) :=
  (regularChart hw₁ hw₂ i).open_target.preimage
    (continuous_const.add (continuous_id.smul continuous_const))

theorem zero_mem_timeDomain {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w)
    (hx : x ∈ (regularChart hw₁ hw₂ i).source) : 0 ∈ timeDomain hw₁ hw₂ i v x := by
  change regularChart hw₁ hw₂ i x + (0 : ℝ) • v ∈ (regularChart hw₁ hw₂ i).target
  rw [zero_smul, add_zero]
  exact (regularChart hw₁ hw₂ i).map_source hx

theorem curve_zero {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w)
    (hx : x ∈ (regularChart hw₁ hw₂ i).source) : curve hw₁ hw₂ i v x 0 = x := by
  simp only [curve, zero_smul, add_zero]
  exact (regularChart hw₁ hw₂ i).left_inv hx

theorem curve_mem_source {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ)
    (ht : t ∈ timeDomain hw₁ hw₂ i v x) :
    curve hw₁ hw₂ i v x t ∈ (regularChart hw₁ hw₂ i).source :=
  (regularChart hw₁ hw₂ i).map_target ht

theorem coordinates_curve {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ)
    (ht : t ∈ timeDomain hw₁ hw₂ i v x) :
    regularChart hw₁ hw₂ i (curve hw₁ hw₂ i v x t) = regularChart hw₁ hw₂ i x + t • v :=
  (regularChart hw₁ hw₂ i).right_inv ht

theorem continuousOn_curve {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) :
    ContinuousOn (curve hw₁ hw₂ i v x) (timeDomain hw₁ hw₂ i v x) :=
  (regularChart hw₁ hw₂ i).continuousOn_symm.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn (fun _ ht => ht)

theorem curve_add {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) (s t : ℝ)
    (hs : s ∈ timeDomain hw₁ hw₂ i v x) :
    curve hw₁ hw₂ i v (curve hw₁ hw₂ i v x s) t = curve hw₁ hw₂ i v x (s + t) := by
  change (regularChart hw₁ hw₂ i).symm
      (regularChart hw₁ hw₂ i (curve hw₁ hw₂ i v x s) + t • v) =
    (regularChart hw₁ hw₂ i).symm (regularChart hw₁ hw₂ i x + (s + t) • v)
  rw [coordinates_curve hw₁ hw₂ i v x s hs]
  rw [add_smul, add_assoc]

theorem hasDerivAt_coordinates {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w) (t : ℝ)
    (ht : t ∈ timeDomain hw₁ hw₂ i v x) :
    HasDerivAt (fun s => regularChart hw₁ hw₂ i (curve hw₁ hw₂ i v x s)) v t := by
  have hline : HasDerivAt (fun s : ℝ => regularChart hw₁ hw₂ i x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add (regularChart hw₁ hw₂ i x)
  apply hline.congr_of_eventuallyEq
  filter_upwards [(timeDomain_open hw₁ hw₂ i v x).mem_nhds ht] with s hs
  exact coordinates_curve hw₁ hw₂ i v x s hs

theorem curves_agree_near_zero {L₁ L₂ : Lattice} {w : Plane}
    (hw₁ : L₁.EmbeddedSlit w) (hw₂ : L₂.EmbeddedSlit w)
    (i j : Index L₁ L₂ w) (v : Plane) (x : Regular L₁ L₂ w)
    (hxi : x ∈ (regularChart hw₁ hw₂ i).source)
    (hxj : x ∈ (regularChart hw₁ hw₂ j).source) :
    ∀ᶠ t in 𝓝 (0 : ℝ), curve hw₁ hw₂ i v x t = curve hw₁ hw₂ j v x t := by
  let e := regularChart hw₁ hw₂ i
  let d := regularChart hw₁ hw₂ j
  let F := e.symm.trans d
  have hFsource : e x ∈ F.source := by
    refine ⟨e.map_source hxi, ?_⟩
    change e.symm (e x) ∈ d.source
    rw [e.left_inv hxi]
    exact hxj
  obtain ⟨a, ha⟩ := RegularTranslationStructure.regular_transition_property hw₁ hw₂ i j _ hFsource
  have hcenter : F (e x) = d x := by
    change d (e.symm (e x)) = d x
    rw [e.left_inv hxi]
  have ha0 : d x = e x + a := hcenter.symm.trans ha.self_of_nhds
  have hline : Continuous (fun t : ℝ => e x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hFnear : ∀ᶠ t in 𝓝 (0 : ℝ), e x + t • v ∈ F.source := by
    apply hline.continuousAt
    simpa only [zero_smul, add_zero] using F.open_source.mem_nhds hFsource
  have htranslation : ∀ᶠ t in 𝓝 (0 : ℝ), F (e x + t • v) = (e x + t • v) + a := by
    apply Filter.Tendsto.eventually _ ha
    simpa only [zero_smul, add_zero] using hline.tendsto (0 : ℝ)
  filter_upwards [hFnear, htranslation] with t ht htrans
  have heq : d (e.symm (e x + t • v)) = d x + t • v := by
    change F (e x + t • v) = _
    rw [htrans, ha0]
    abel
  change e.symm (e x + t • v) = d.symm (d x + t • v)
  rw [← heq]
  exact (d.left_inv ht.2).symm

end MNEC.LocalDirectionalCurves
