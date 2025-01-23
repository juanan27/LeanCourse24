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
  exact ω_integer γ z h
}
obtain ⟨n, hn⟩ := h1
rw [hn]
have h2 : ω z (closed_curve_reverse γ) = -n := by {
  have h₁ : (closed_curve_reverse γ) = (fun t => γ (1-t)) := by {
    ext1 x
    simp only [closed_curve_reverse, closed_curve]
  }
  unfold ω
  rw [h₁]
  have h₂ : (fun t => γ (1 - t)) = (γ ∘ (λ t => 1 - t)) := by {
    ext1 x
    simp
  }
  have h₃ : deriv (fun t => γ (1 - t)) = - (deriv γ) := by {
    ext1 x
    rw [h₂]
    have h4 : DifferentiableAt ℝ γ ((fun (t : ℝ) => 1 - t) x) := by {
      simp
      have h5 : Differentiable ℝ γ := by exact closed_curve.Diff γ
      exact h5.differentiableAt
    }
    have h5 : DifferentiableAt ℝ (λ t => 1 - t) x := by {
      have h6 : DifferentiableAt ℝ id x := by {
        exact differentiableAt_id
      }
      have h7 : DifferentiableAt ℝ (fun t => (1 : ℝ)) x := by {
        exact differentiableAt_const 1
      }
      exact DifferentiableAt.sub h7 h6
    }
    sorry
  }
  rw [h₃]
  sorry
}
rw [h2]
sorry
}
