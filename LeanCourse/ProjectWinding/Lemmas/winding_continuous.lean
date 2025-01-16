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

-- CHANGE PROOF TO THE CLASSICAL ONE

theorem ω_continuous {t : ℝ} (γ : closed_curve) (z : ℂ) (h : ∀ z ∈ (univ \ (image γ I)), γ t - z ≠ 0)
: ContinuousOn ω (univ \ (image γ I))  := by {
  /- intro z₀ hz₀
  unfold ω
  simp
  intro x hx
  simp -/
  unfold ω

  let f :=
    (fun z ↦ ∫ (t : ℝ) in (0)..(1), deriv γ.toFun t / (γ.toFun t - z))

  let g := fun s z => deriv γ.toFun s / (γ.toFun s - z)

  /-have equal : (fun z ↦ ∫ (s : ℝ) in (0)..(1), deriv γ.toFun s / (γ.toFun s - z)) =
  (fun z ↦ ∫ (s : ℝ) in (0)..(1), g s z) := by {
    ext1 x
    unfold g
    rfl
  }-/

  have h_cont : ContinuousOn f (univ \ (image γ I)) := by {
    --intro x hx
    unfold f
    --refine ContinuousAt.continuousWithinAt ?h
    have h_aux : ContinuousOn (g t) (univ \ (image γ I)) := by{
      unfold g
      have hf : ContinuousOn (fun z => deriv γ t) (univ \ (image γ I)) := by {
        exact continuousOn_const
      }
      have hg : ContinuousOn (fun z => γ.toFun t - z) (univ \ (image γ I)) := by {
        have hg1 : ContinuousOn (fun z => γ.toFun t) (univ \ (image γ I)) := by {
          exact continuousOn_const
        }
        have hg2 : ContinuousOn (fun z => z) (univ \ (image γ I)) := by {
          exact continuousOn_id' (Set.univ \ γ.toFun '' I)
        }
        apply ContinuousOn.sub
        · exact hg1
        · exact hg2
      }
      exact ContinuousOn.div hf hg h
    }
    unfold g at h_aux
    sorry
  }
  sorry
}


#min_imports
