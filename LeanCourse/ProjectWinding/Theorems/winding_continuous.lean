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


theorem ω_continuous (γ : closed_curve) (z : ℂ) (h : z ∉ γ '' I)
: ContinuousOn (fun z => 1/(2*Real.pi*Complex.I) *  ∫ t in I, (deriv γ t) / (γ t - z)) ((univ \ (image γ I)) : Set ℂ )  := by {
  rw[Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  sorry
}
