import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.GroupWithZero.Basic
import LeanCourse.ProjectWinding.Definitions.curves

open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

-- The index function is continuous

theorem ω_cont (γ : closed_curve) (z : ℂ) (h : ∀ t ∈ I, γ t ≠ z)
: ContinuousOn ω (univ \ (image γ I))  := by {
  /- intro z₀ hz₀
  unfold ω
  simp
  intro x hx
  simp -/
  let f : ℂ → ℂ :=
    (fun z ↦ ∫ (t : ℝ) in (0)..(1), deriv γ.toFun t / (γ.toFun t - z))

  have h_cont : ContinuousOn f (univ \ (image γ I)) := by {
    intro x hx
    unfold f
    refine ContinuousAt.continuousWithinAt ?h
    have h_aux : ContinuousOn (fun z => deriv γ.toFun  / (γ.toFun - z)) (univ \ (image γ I)) := by {
    sorry
    }
  sorry
  }
  sorry
}
