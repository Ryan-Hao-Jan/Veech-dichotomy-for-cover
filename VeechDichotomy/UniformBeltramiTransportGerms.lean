module

public import VeechDichotomy.UniformBeltramiTransportFormulas

/-! Genuine joint holomorphic germs for the actual whole-surface
transports and inverses. The proof uses explicit addition/subtraction in
complex coordinates and the actual holomorphic total chart inverse. -/

@[expose] public section
noncomputable section

namespace VeechDichotomy.UniformBeltramiTransportGerms

open MNEC.NativeAbelianDifferential BeltramiPlane Set Filter Metric Topology
open UniformBeltramiMarkData UniformBeltramiMarkTransport UniformBeltramiTransportFormulas
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {m : ℕ}

def forwardInput (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) : ℂ × ℂ :=
  (p.1.1, p.2 + p.1.2 i)

def inverseInput (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ) : ℂ × ℂ :=
  (p.1.1, p.2 - p.1.2 i)

theorem forwardInput_contDiff (i : Fin m) : ContDiff ℂ ω (forwardInput i) :=
  (contDiff_fst.comp contDiff_fst).prodMk
    (contDiff_snd.add ((ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).contDiff.comp
      (contDiff_snd.comp contDiff_fst)))

theorem inverseInput_contDiff (i : Fin m) : ContDiff ℂ ω (inverseInput i) :=
  (contDiff_fst.comp contDiff_fst).prodMk
    (contDiff_snd.sub ((ContinuousLinearMap.proj i : (Fin m → ℂ) →L[ℂ] ℂ).contDiff.comp
      (contDiff_snd.comp contDiff_fst)))

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {q : Differential X} {b : Fin m → X} {μ₀ : Parameter} {A : Data q b μ₀} (F : Family A)

theorem forward_holomorphicAt (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    (ha : p.1 ∈ ComplexBeltramiMarkParameters.domain A) (hz : ‖p.2‖ < 1) :
    ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) 𝓘(ℂ, ℂ × ℂ) ω
      (ambientForward F i) p := by
  let a := ambientParameters (A := A) p.1
  have hn : ‖p.2 + p.1.2 i‖ ≤ 2 := by
    have hδ := ha.2.2 i
    exact (norm_add_le _ _).trans (by linarith)
  have hInv := NormalizedBeltramiTotalInverse.uniform_holomorphicAt (A.disks i) (A.localBase a.1 i) hn
  change ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω
    (NormalizedBeltramiTotalInverse.inverse (A.disks i)) (a.1.val.val, p.2 + p.1.2 i) at hInv
  rw [(parameter_values ha).1] at hInv
  apply (hInv.comp p ((forwardInput_contDiff i).contMDiff p)).congr_of_eventuallyEq
  have hparam := ((ComplexBeltramiMarkParameters.domain_open A).preimage
    (continuous_fst : Continuous (fun z : ComplexBeltramiMarkParameters.Space (m := m) × ℂ => z.1))).mem_nhds ha
  have hcoord : IsOpen {z : ComplexBeltramiMarkParameters.Space (m := m) × ℂ | ‖z.2‖ < 1} :=
    isOpen_lt continuous_snd.norm continuous_const
  filter_upwards [hparam, hcoord.mem_nhds hz] with z hza hzz
  exact forward_formula F i z hza hzz

theorem inverse_holomorphicAt (i : Fin m) (p : ComplexBeltramiMarkParameters.Space (m := m) × ℂ)
    (ha : p.1 ∈ ComplexBeltramiMarkParameters.domain A) (hw : ‖p.2 - p.1.2 i‖ < 1) :
    ContMDiffAt 𝓘(ℂ, ComplexBeltramiMarkParameters.Space (m := m) × ℂ) 𝓘(ℂ, ℂ × ℂ) ω
      (ambientInverse F i) p := by
  let a := ambientParameters (A := A) p.1
  have hn : ‖p.2 - p.1.2 i‖ ≤ 2 := by linarith
  have hInv := NormalizedBeltramiTotalInverse.uniform_holomorphicAt (A.disks i) (A.localBase a.1 i) hn
  change ContMDiffAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) ω
    (NormalizedBeltramiTotalInverse.inverse (A.disks i)) (a.1.val.val, p.2 - p.1.2 i) at hInv
  rw [(parameter_values ha).1] at hInv
  apply (hInv.comp p ((inverseInput_contDiff i).contMDiff p)).congr_of_eventuallyEq
  have hparam := ((ComplexBeltramiMarkParameters.domain_open A).preimage
    (continuous_fst : Continuous (fun z : ComplexBeltramiMarkParameters.Space (m := m) × ℂ => z.1))).mem_nhds ha
  have hcoord : IsOpen {z : ComplexBeltramiMarkParameters.Space (m := m) × ℂ | ‖z.2 - z.1.2 i‖ < 1} :=
    isOpen_lt (continuous_snd.sub ((continuous_apply i).comp (continuous_snd.comp continuous_fst))).norm continuous_const
  filter_upwards [hparam, hcoord.mem_nhds hw] with z hza hzw
  exact inverse_formula F i z hza hzw

end VeechDichotomy.UniformBeltramiTransportGerms
