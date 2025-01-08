import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.UnitInterval
import LeanCourse.ProjectWinding.Definitions.curves

open DifferentiableOn Set unitInterval Finset Metric

noncomputable section

open Classical

-- We can see the complex plane divided by the interior, exterior and image of any closed curve:

lemma interior_exterior_OfClosedCurve_whole_plane (γ : closed_curve) :
∀ z : ℂ, z ∈ interiorOfClosedCurve γ ∪ exteriorOfClosedCurve γ ∪ imageOfClosedCurve γ := by {
  intro z
  by_cases h : z ∈ γ '' I
  · exact Set.mem_union_right (interiorOfClosedCurve γ ∪ exteriorOfClosedCurve γ) h
  · by_cases h₀ : ω z γ = 0
    · have h₀' : z ∈ exteriorOfClosedCurve γ := by {
      unfold exteriorOfClosedCurve
      simp only [Set.mem_Icc, not_exists, not_and, and_imp, mem_setOf_eq]
      trivial
      }
      simp[h₀']
    · have h₀' : z ∈ interiorOfClosedCurve γ := by {
      unfold interiorOfClosedCurve
      simp only [Set.mem_Icc, not_exists, not_and, and_imp, mem_setOf_eq]
      trivial}
      simp[h₀']

}
