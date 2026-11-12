module

public import VeechDichotomy.Configuration
public import VeechDichotomy.CompactLift

/-!
The genuine quotient of deformations and marked tuples by an affine
group with derivative homomorphism D. It is not yet identified with the
paper's moduli space of marked quadratic differentials.
-/

@[expose] public section

open Set Topology

namespace VeechDichotomy

variable {G H Z : Type*} [Group G] [Group H] [MulAction H Z]

/-- `(A,b)` and `(A Dφ, φ⁻¹ b)` represent the same marked deformation. -/
def markedRelation (D : H →* G) : Setoid (G × Z) where
  r u v := ∃ a : H, v.1 = u.1 * D a ∧ v.2 = a⁻¹ • u.2
  iseqv := by
    constructor
    · intro u
      exact ⟨1, by simp, by simp⟩
    · rintro u v ⟨a, ha, hb⟩
      refine ⟨a⁻¹, ?_, ?_⟩
      · simp [ha, mul_assoc]
      · simp [hb]
    · rintro u v w ⟨a, ha, hb⟩ ⟨b, hc, hd⟩
      refine ⟨a * b, ?_, ?_⟩
      · simp [hc, ha, mul_assoc]
      · simp [hd, hb, mul_smul]

def MarkedOrbit (D : H →* G) (Z : Type*) [MulAction H Z] :=
  Quotient (markedRelation (Z := Z) D)

instance markedOrbitTopology (D : H →* G) [TopologicalSpace G] [TopologicalSpace Z] :
    TopologicalSpace (MarkedOrbit D Z) :=
  inferInstanceAs (TopologicalSpace (Quotient (markedRelation (Z := Z) D)))

def markedClass (D : H →* G) (u : G × Z) : MarkedOrbit D Z :=
  Quotient.mk (markedRelation D) u

theorem markedClass_normalize (D : H →* G) (A : G) (b : Z) (a : H) :
    markedClass D (A, b) = markedClass D (A * D a, a⁻¹ • b) :=
  Quotient.sound ⟨a, rfl, rfl⟩

theorem continuous_markedClass (D : H →* G)
    [TopologicalSpace G] [TopologicalSpace Z] : Continuous (markedClass (Z := Z) D) :=
  continuous_quot_mk

/-- All normalized marked deformations above a compact base return set
belong to one compact subset of the actual marked-deformation quotient. -/
theorem compact_marked_returns (D : H →* G)
    [TopologicalSpace G] [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    [TopologicalSpace Z] {F : Set Z} (hF : IsCompact F) (hFi : invariant H F)
    {b : Z} (hb : b ∈ F)
    {C : Set (G ⧸ D.range)} (hC : IsCompact C) :
    ∃ B : Set (MarkedOrbit D Z), IsCompact B ∧
      ∀ A : G, (QuotientGroup.mk A : G ⧸ D.range) ∈ C →
        markedClass D (A, b) ∈ B := by
  obtain ⟨K, hK, hnorm⟩ := exists_compact_right_normalizers D.range hC
  refine ⟨markedClass D '' (K ×ˢ F),
    (hK.prod hF).image (continuous_markedClass D), ?_⟩
  intro A hA
  obtain ⟨γ, hγ⟩ := hnorm A hA
  obtain ⟨a, ha⟩ := γ.property
  rw [markedClass_normalize D A b a]
  apply mem_image_of_mem
  refine ⟨?_, hFi a⁻¹ hb⟩
  simpa only [ha] using hγ

end VeechDichotomy
