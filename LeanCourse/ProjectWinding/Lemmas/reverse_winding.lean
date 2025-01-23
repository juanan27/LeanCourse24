import LeanCourse.ProjectWinding.Definitions.curves
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import LeanCourse.ProjectWinding.Theorems.winding_integer
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.SetIntegral

open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

lemma ω_reverse (γ : closed_curve) (z : ℂ) (h : ∀ t : ℝ , γ t ≠ z) : ω z γ = - ω z (closed_curve_reverse γ) := by {
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
  have h₂ : (fun (t : ℝ) => γ (1 - t)) = (γ ∘ (λ (t : ℝ) => ((1 - t) : ℝ))) := by {
    ext1 x
    simp
  }
  have h₃ : ∀ t : ℝ,  deriv (fun (t : ℝ) => γ (1 - t)) t = - (deriv γ) (1 - t) := by {
    intro t
    rw [h₂]
    have h4 : DifferentiableAt ℝ γ ((fun (t : ℝ) => ((1 - t) : ℝ)) t) := by {
      simp
      have h5 : Differentiable ℝ γ := by exact closed_curve.Diff γ
      exact h5.differentiableAt
    }
    have h5 : DifferentiableAt ℝ (λ (t : ℝ) => ((1 - t) : ℝ)) t := by {
      have h6 : DifferentiableAt ℝ id t := by {
        exact differentiableAt_id
      }
      have h7 : DifferentiableAt ℝ (fun (_ : ℝ) => (1 : ℝ)) t := by {
        exact differentiableAt_const 1
      }
      exact DifferentiableAt.sub h7 h6
    }
    have h6 : deriv (γ ∘ fun (t : ℝ) ↦ ((1 - t) : ℝ)) t = deriv γ ((fun (t : ℝ) => 1 - t) t) * deriv (fun (t : ℝ) => ((1 - t) : ℝ)) t := by {
      have h9 : NormedSpace ℝ ℝ := by infer_instance
      --exact deriv.comp h4 h5
      sorry
    }
    rw [h6]
    have h7 : deriv (fun (t : ℝ) => ((1 - t) : ℝ)) t = -1 := by {
      let f : ℝ → ℝ := fun t => 1
      have h8 : deriv f t = 0 := by {
        sorry
      }
      have h9 : deriv (λ (t : ℝ) => t) t = 1 := by {
        sorry
      }
      --exact deriv_sub h8 h9
      sorry
    }
    rw [h7]
    simp
  }
  simp only [h₃]
  have heq : ∀ t : ℝ, deriv (fun t ↦ γ.toFun (1 - t)) t / (γ.toFun (1 - t) - z) =
    -deriv γ (1 - t) / (γ (1 - t) - z) := by {
    intro t
    rw [h₃]
  }
  have hs : MeasurableSet I := by exact measurableSet_Icc
  have haux : EqOn (fun t => deriv (fun t ↦ γ.toFun (1 - t)) t / (γ.toFun (1 - t) - z)) (fun t => - deriv γ (1 - t) / (γ (1 - t) - z)) I := by {
    intros x hx
    simp
    rw [heq]
  }
  have haux1 : ∀ t : ℝ, -deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z) =
  - (deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z)) := by {
    intro t
    ring
  }
  have neg : 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, - (deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z)) =
    - (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z)) := by {
    rw [integral_neg]
    simp
  }
  simp only [haux1]
  rw [neg]
  have hint : ∫ (t : ℝ) in I, deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z) =
    ∫ (x : ℝ) in (1)..(0), deriv γ x / (γ x - z) := by {
      sorry
  }
  rw [hint]
  have hint1 : ∫ (x : ℝ) in (1)..(0), deriv γ x / (γ x - z) = - ∫ (x : ℝ) in (0)..(1), deriv γ x / (γ x - z) := by {
    exact intervalIntegral.integral_symm 0 1
  }
  rw [hint1]
  sorry
}
rw [h2]
ring
}
