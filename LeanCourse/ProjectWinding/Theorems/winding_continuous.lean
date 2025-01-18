import LeanCourse.ProjectWinding.Definitions.curves
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.MetricSpace.Pseudo.Defs


open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

-- The index function is continuous

-- CHANGE PROOF TO THE CLASSICAL ONE

theorem ω_continuous {t : ℝ} (γ : closed_curve) (z : ℂ) (h : ∀ z ∈ (univ \ (image γ I)), γ t - z ≠ 0)
: ContinuousOn ω (univ \ (image γ I))  := by {
  sorry
}
