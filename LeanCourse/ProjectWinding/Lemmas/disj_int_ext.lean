import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.UnitInterval
import LeanCourse.ProjectWinding.Definitions.curves

open DifferentiableOn Finset Set unitInterval

noncomputable section

open Classical

/- This lemma basically shows the definitions we gave for:

   · Exterior of a curve
   · Interior of a curve
   · Image of a curve

are consistent.
-/


lemma disjoint_interior_exterior_OfClosedCurve (γ : closed_curve):
interiorOfClosedCurve γ ∩ exteriorOfClosedCurve γ ∩ imageOfClosedCurve γ = ∅ := by {
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and, and_imp]
  intro h₀ h₁
  exfalso
  have h0 : ω z γ = 0 := by {
    unfold exteriorOfClosedCurve at *
    have haux : ω z γ = 0 ∧ z ∉ γ.toFun '' I := by exact h₁
    obtain ⟨hp, hq⟩ := haux
    exact hp
  }
  have h1 : ω z γ ≠ 0 := by {
    unfold interiorOfClosedCurve at *
    have haux : ω z γ ≠  0 ∧ z ∉ γ.toFun '' I := by exact h₀
    obtain ⟨hp, hq⟩ := haux
    exact hp
  }
  contradiction
}
