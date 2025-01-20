import LeanCourse.ProjectWinding.Definitions.curves
import Mathlib.MeasureTheory.Integral.IntervalIntegral


open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

lemma ω_reverse {t : ℝ} (γ : closed_curve) (z : ℂ) : ω z γ = - ω z (closed_curve_reverse γ) := by {
unfold ω closed_curve_reverse
simp only
sorry
}
