import LeanCourse.ProjectWinding.Definitions.curves
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import LeanCourse.ProjectWinding.Theorems.winding_integer


open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

lemma ω_reverse {t : ℝ} (γ : closed_curve) (z : ℂ) (h : ∀ t : ℝ , γ t ≠ z) : ω z γ = - ω z (closed_curve_reverse γ) := by {
have h1 : ∃ n : ℤ, ω z γ = n := by {
  sorry -- import winding_intenger (gonna do it later as it takes a while...)
}
obtain ⟨n, hn⟩ := h1
rw [hn]
have h2 : ω z (closed_curve_reverse γ) = -n := by {
  sorry -- import winding_intenger (gonna do it later as it takes a while...)
}
rw [h2]
ring
}
