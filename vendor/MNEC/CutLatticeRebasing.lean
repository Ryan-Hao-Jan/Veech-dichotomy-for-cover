module

public import MNEC.PrimitiveLatticeRebasing
public import MNEC.CutTorusBoundary

@[expose] public section

/-!
# Physical lattice coordinate changes on the actual cut topology

A homeomorphism of coordinate tori compatible with physical projections
preserves slit parameters, banks and all physical bank-neighborhood
generators. It therefore induces an actual homeomorphism of the cut tori.
The primitive-period specialization uses the computed Bezout basis.
No cut or glued-surface homeomorphism is assumed as an input.
-/

noncomputable section

namespace MNEC.CutLatticeRebasing

open LatticeTorus CutTorus CutBankLifts CutTorusBoundary Set Topology

/-- Source coordinates are those of `M`, target coordinates those of `L`.
Only the coordinate-torus map and its physical projection law are inputs.
The topology of cut points is not part of this record. -/
structure PhysicalTorusEquiv (L M : Lattice) where
  torus : Torus ≃ₜ Torus
  project_eq : ∀ x : Plane, torus (M.project x) = L.project x

namespace PhysicalTorusEquiv

variable {L M : Lattice}

def refl (L : Lattice) : PhysicalTorusEquiv L L where
  torus := Homeomorph.refl Torus
  project_eq _ := rfl

def symm (e : PhysicalTorusEquiv L M) : PhysicalTorusEquiv M L where
  torus := e.torus.symm
  project_eq x := by
    apply e.torus.injective
    rw [Homeomorph.apply_symm_apply, e.project_eq]

def primitive (L : Lattice) (m n : ℤ) (h : PrimitiveLatticeRebasing.Primitive m n) :
    PhysicalTorusEquiv L (PrimitiveLatticeRebasing.rebased L m n h) where
  torus := PrimitiveLatticeRebasing.torusHomeomorph m n h
  project_eq := PrimitiveLatticeRebasing.torusHomeomorph_project L m n h

theorem project_eq_iff (e : PhysicalTorusEquiv L M) (x : Plane) (q : Torus) :
    L.project x = e.torus q ↔ M.project x = q := by
  constructor
  · intro h
    exact e.torus.injective ((e.project_eq x).trans h)
  · intro h
    exact (e.project_eq x).symm.trans (congrArg e.torus h)

theorem arc_eq (e : PhysicalTorusEquiv L M) (w : Plane) (t : Parameter) :
    e.torus (M.arc w t) = L.arc w t := e.project_eq ((t : ℝ) • w)

theorem mem_interior_iff (e : PhysicalTorusEquiv L M) (w : Plane) (q : Torus) :
    e.torus q ∈ interior L w ↔ q ∈ interior M w := by
  constructor
  · rintro ⟨t, ht, ht', heq⟩
    exact ⟨t, ht, ht', (e.project_eq_iff _ q).mp heq⟩
  · rintro ⟨t, ht, ht', heq⟩
    exact ⟨t, ht, ht', (e.project_eq_iff _ q).mpr heq⟩

theorem mem_slitSet_iff (e : PhysicalTorusEquiv L M) (w : Plane) (q : Torus) :
    e.torus q ∈ L.slitSet w ↔ q ∈ M.slitSet w := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, e.torus.injective ((e.arc_eq w t).trans ht)⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, (e.arc_eq w t).symm.trans (congrArg e.torus ht)⟩

def map (e : PhysicalTorusEquiv L M) (w : Plane) (p : Point M w) : Point L w :=
  ⟨(e.torus (base p), bank p), p.property.elim Or.inl
    (fun hi => Or.inr ((e.mem_interior_iff w (base p)).mpr hi))⟩

@[simp] theorem base_map (e : PhysicalTorusEquiv L M) (w : Plane) (p : Point M w) :
    base (e.map w p) = e.torus (base p) := rfl

@[simp] theorem bank_map (e : PhysicalTorusEquiv L M) (w : Plane) (p : Point M w) :
    bank (e.map w p) = bank p := rfl

@[simp] theorem map_upper (e : PhysicalTorusEquiv L M) (w : Plane) (q : Torus) :
    e.map w (upper M w q) = upper L w (e.torus q) := by
  apply point_ext <;> rfl

@[simp] theorem map_lower (e : PhysicalTorusEquiv L M) (w : Plane) (q : Torus)
    (hq : q ∈ interior M w) :
    e.map w (lower M w q hq) =
      lower L w (e.torus q) ((e.mem_interior_iff w q).mpr hq) := by
  apply point_ext <;> rfl

@[simp] theorem map_interiorBank (e : PhysicalTorusEquiv L M) (w : Plane)
    (k : Bool) (t : ℝ) (ht : 0 < t ∧ t < 1) :
    e.map w (interiorBank M w k t ht) = interiorBank L w k t ht := by
  apply point_ext
  · exact e.project_eq (t • w)
  · rfl

@[simp] theorem map_boundaryArc (e : PhysicalTorusEquiv L M) (w : Plane)
    (k : Bool) (t : Parameter) :
    e.map w (boundaryArc M w k t) = boundaryArc L w k t := by
  apply point_ext
  · exact e.arc_eq w t
  · rfl

@[simp] theorem symm_map_map (e : PhysicalTorusEquiv L M) (w : Plane) (p : Point M w) :
    e.symm.map w (e.map w p) = p := by
  apply point_ext
  · exact e.torus.symm_apply_apply (base p)
  · rfl

@[simp] theorem map_symm_map (e : PhysicalTorusEquiv L M) (w : Plane) (p : Point L w) :
    e.map w (e.symm.map w p) = p := by
  apply point_ext
  · exact e.torus.apply_symm_apply (base p)
  · rfl

theorem preimage_bankNeighborhood (e : PhysicalTorusEquiv L M) (w : Plane)
    (a b r : ℝ) (k : Bool) :
    e.map w ⁻¹' bankNeighborhood L w a b r k = bankNeighborhood M w a b r k := by
  ext p
  simp only [Set.mem_preimage, bankNeighborhood, Set.mem_ofPred_eq, base_map,
    bank_map, e.mem_slitSet_iff, e.project_eq_iff]

theorem continuous_map (e : PhysicalTorusEquiv L M) (w : Plane) : Continuous (e.map w) := by
  apply continuous_generateFrom_iff.mpr
  intro U hU
  rcases hU with ⟨V, hV, rfl⟩ | ⟨a, b, r, k, ha, hab, hb, hr, rfl⟩
  · have hpre : e.map w ⁻¹' (base ⁻¹' V) = base ⁻¹' (e.torus ⁻¹' V) := rfl
    rw [hpre]
    exact base_preimage_open M w _ (hV.preimage e.torus.continuous)
  · rw [e.preimage_bankNeighborhood]
    exact bankNeighborhood_open M w a b r k ha hab hb hr

def cutHomeomorph (e : PhysicalTorusEquiv L M) (w : Plane) : Point M w ≃ₜ Point L w where
  toFun := e.map w
  invFun := e.symm.map w
  left_inv := e.symm_map_map w
  right_inv := e.map_symm_map w
  continuous_toFun := e.continuous_map w
  continuous_invFun := e.symm.continuous_map w

@[simp] theorem base_cutHomeomorph (e : PhysicalTorusEquiv L M) (w : Plane) (p : Point M w) :
    base (e.cutHomeomorph w p) = e.torus (base p) := rfl

@[simp] theorem bank_cutHomeomorph (e : PhysicalTorusEquiv L M) (w : Plane) (p : Point M w) :
    bank (e.cutHomeomorph w p) = bank p := rfl

@[simp] theorem cutHomeomorph_upper (e : PhysicalTorusEquiv L M) (w : Plane) (q : Torus) :
    e.cutHomeomorph w (upper M w q) = upper L w (e.torus q) := e.map_upper w q

@[simp] theorem cutHomeomorph_lower (e : PhysicalTorusEquiv L M) (w : Plane) (q : Torus)
    (hq : q ∈ interior M w) :
    e.cutHomeomorph w (lower M w q hq) =
      lower L w (e.torus q) ((e.mem_interior_iff w q).mpr hq) := e.map_lower w q hq

@[simp] theorem cutHomeomorph_upper_project (e : PhysicalTorusEquiv L M) (w x : Plane) :
    e.cutHomeomorph w (upper M w (M.project x)) = upper L w (L.project x) := by
  rw [e.cutHomeomorph_upper, e.project_eq]

@[simp] theorem cutHomeomorph_lower_project (e : PhysicalTorusEquiv L M) (w : Plane)
    (t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    e.cutHomeomorph w (lower M w (M.project (t • w)) ⟨t, ht, ht', rfl⟩) =
      lower L w (L.project (t • w)) ⟨t, ht, ht', rfl⟩ := by
  apply point_ext
  · exact e.project_eq (t • w)
  · rfl

@[simp] theorem cutHomeomorph_interiorBank (e : PhysicalTorusEquiv L M) (w : Plane)
    (k : Bool) (t : ℝ) (ht : 0 < t ∧ t < 1) :
    e.cutHomeomorph w (interiorBank M w k t ht) = interiorBank L w k t ht :=
  e.map_interiorBank w k t ht

@[simp] theorem cutHomeomorph_boundaryArc (e : PhysicalTorusEquiv L M) (w : Plane)
    (k : Bool) (t : Parameter) :
    e.cutHomeomorph w (boundaryArc M w k t) = boundaryArc L w k t :=
  e.map_boundaryArc w k t

end PhysicalTorusEquiv

def rebasedCutHomeomorph (L : Lattice) (w : Plane) (m n : ℤ)
    (h : PrimitiveLatticeRebasing.Primitive m n) :
    Point (PrimitiveLatticeRebasing.rebased L m n h) w ≃ₜ Point L w :=
  (PhysicalTorusEquiv.primitive L m n h).cutHomeomorph w

@[simp] theorem rebasedCutHomeomorph_bank (L : Lattice) (w : Plane) (m n : ℤ)
    (h : PrimitiveLatticeRebasing.Primitive m n)
    (p : Point (PrimitiveLatticeRebasing.rebased L m n h) w) :
    bank (rebasedCutHomeomorph L w m n h p) = bank p := rfl

@[simp] theorem rebasedCutHomeomorph_upper_project (L : Lattice) (w : Plane) (m n : ℤ)
    (h : PrimitiveLatticeRebasing.Primitive m n) (x : Plane) :
    rebasedCutHomeomorph L w m n h
      (upper (PrimitiveLatticeRebasing.rebased L m n h) w
        ((PrimitiveLatticeRebasing.rebased L m n h).project x)) = upper L w (L.project x) :=
  (PhysicalTorusEquiv.primitive L m n h).cutHomeomorph_upper_project w x

@[simp] theorem rebasedCutHomeomorph_interiorBank (L : Lattice) (w : Plane) (m n : ℤ)
    (h : PrimitiveLatticeRebasing.Primitive m n) (k : Bool) (t : ℝ) (ht : 0 < t ∧ t < 1) :
    rebasedCutHomeomorph L w m n h
      (interiorBank (PrimitiveLatticeRebasing.rebased L m n h) w k t ht) =
      interiorBank L w k t ht :=
  (PhysicalTorusEquiv.primitive L m n h).cutHomeomorph_interiorBank w k t ht

@[simp] theorem rebasedCutHomeomorph_boundaryArc (L : Lattice) (w : Plane) (m n : ℤ)
    (h : PrimitiveLatticeRebasing.Primitive m n) (k : Bool) (t : Parameter) :
    rebasedCutHomeomorph L w m n h
      (boundaryArc (PrimitiveLatticeRebasing.rebased L m n h) w k t) = boundaryArc L w k t :=
  (PhysicalTorusEquiv.primitive L m n h).cutHomeomorph_boundaryArc w k t

end MNEC.CutLatticeRebasing

