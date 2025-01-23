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
import Mathlib.Tactic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Function.L1Space
import LeanCourse.ProjectWinding.Definitions.curves


open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
--open scoped Real NNReal Interval Pointwise Topology
open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics
open Set unitInterval Finset Metric

lemma division_continuous {f : ℝ → ℂ}  {g : ℝ → ℂ}  (h : ContinuousOn f I)
(h' : ContinuousOn g I) (h_v : ∀ s ∈ I, g s ≠ 0) : ContinuousOn (fun s ↦ f s / g s) I := by {
apply h.div
exact h'
exact fun x a ↦ h_v x a
}

lemma division_continuous_ball {f : ℂ → ℂ} {g : ℂ → ℂ} (h : ContinuousOn f $ closedBall 0 1)
(h' : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ f s / g s) (closedBall 0 1) := by {
  apply h.div
  exact h'
  exact fun x a ↦ h_v x a}

lemma inverse_continuous_ball (g : ℂ → ℂ)
(h : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ 1 / g s) (closedBall 0 1) := by {
  let f : ℂ → ℂ := fun z ↦ 1
  have hf : ContinuousOn f (closedBall 0 1) := by exact continuousOn_const
  have hquot : ContinuousOn (fun s ↦ f s / g s) (closedBall 0 1) := by exact division_continuous_ball hf h h_v
  exact hquot
}
lemma inverse_continuous_ball_2 (g : ℂ → ℂ)
(h : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ (g s)⁻¹) (closedBall 0 1) := by
{
  have hs0 : ∀ s ∈ closedBall 0 1, 1 / g s  = (g s)⁻¹ := by {
    norm_num
  }
  have heq : ContinuousOn (fun s ↦ 1 / (g s)) (closedBall 0 1) ↔ ContinuousOn (fun s ↦ (g s)⁻¹) (closedBall 0 1) := by exact continuousOn_congr hs0
  rw[← heq]
  exact inverse_continuous_ball g h h_v
}
-- We write the same theorems in the differentiable version

lemma division_differentiable (f : ℂ → ℂ ) (g : ℂ → ℂ ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g ) (h₀ : ∀ z, g z ≠ 0):
 Differentiable ℂ (fun s ↦ f s / g s) := by {
  apply hf.div
  trivial
  tauto
 }

lemma inverse_differentiable {g : ℂ → ℂ}
(h : Differentiable ℂ g ) (h_v : ∀ s, g s ≠ 0) : Differentiable ℂ (fun s ↦ 1 / g s)  := by {
let f : ℂ → ℂ := fun z ↦ 1
have hf : Differentiable ℂ f := by exact differentiable_const 1
have hqout : Differentiable ℂ (fun s ↦ 1 / g s) := by exact division_differentiable (fun s ↦ 1) g hf h h_v
exact hqout
}

lemma division_differentiable_ball {f : ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ f z_1) (hg : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1 ) (h₀ : ∀ z, g z ≠ 0):
 ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ f s / g s) z_1 := by {
  intro z_1 h_z1
  specialize hf z_1 h_z1
  specialize hg z_1 h_z1
  apply hf.div
  · exact hg
  · tauto
 }

lemma inverse_differentiable_ball {g : ℂ → ℂ}
(h : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) :
 ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ 1 / g s) s  := by {
  let f : ℂ → ℂ := fun z ↦ 1
  intro s hs
  have hf : ∀ s ∈ closedBall 0 1, DifferentiableAt  ℂ f s := by exact fun s a ↦ differentiableAt_const 1
  have hquot : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ  (fun s ↦ f s / g s) s :=
  by exact fun s a ↦ DifferentiableAt.div (hf s a) (h s a) (h_v s a)
  exact hquot s hs
  }

lemma inverse_differentiable_ball_2 {g : ℂ → ℂ}
(h : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ (g s)⁻¹) s  := by {
  intro s hs
  exact DifferentiableAt.inv (h s hs) (h_v s hs)
}

lemma ftc {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv
-- We prove now that the winding number is always an integer. We introduce the following lemma:

lemma exp_one (z : ℂ) (h_1 : Complex.exp z = 1) : ∃ k : ℤ, z = 2 * Real.pi * k * Complex.I := by {
  have h : Complex.exp z = 1 → ∃ n : ℤ , z = n * (2 * ↑π * Complex.I) := by exact Complex.exp_eq_one_iff.1
  have h' : ∃ n : ℤ , z = ↑n * (2 * ↑π * Complex.I) := h h_1
  obtain ⟨ n, hn ⟩ := h'
  use n
  simp[hn]
  ring
  }
