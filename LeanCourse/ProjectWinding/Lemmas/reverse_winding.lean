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

instance : NormedField ℝ := by exact normedField
instance : NormedSpace ℝ ℂ := by exact NormedSpace.complexToReal
instance : NormedAlgebra ℝ ℝ := by exact RCLike.toNormedAlgebra

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
  have h₃ : ∀ t : ℝ, deriv (fun (t : ℝ) => γ (1 - t)) t = - (deriv γ) (1 - t) := by {
    intro t
    rw [h₂]
    let g : ℝ → ℝ := fun t => 1 - t
    let f : ℝ → ℂ := γ.toFun
    have h4 : DifferentiableAt ℝ f (1 - t) := by {
      --simp
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
    have h6 : deriv (f ∘ g) t =
    deriv f (g t) * deriv g t := by {
      haveI : NormedSpace ℝ ℂ := by exact instNormedSpaceRealComplex_leanCourse
      haveI : NormedAlgebra ℝ ℂ := by exact RCLike.toNormedAlgebra
      sorry
    }
    rw [h6]
    have h7 : deriv (fun (t : ℝ) => ((1 - t) : ℝ)) t = -1 := by {
      let f : ℝ → ℝ := fun t => 1
      have h8 : deriv f t = 0 := by {
        unfold f
        simp
      }
      have h9 : deriv (λ (t : ℝ) => t) t = 1 := by {
        exact deriv_id t
      }
      have h10 : DifferentiableAt ℝ (fun t => (1 : ℝ)) t := by {
        exact differentiableAt_const 1
      }
      have h11 : DifferentiableAt ℝ (λ t => t) t := by {
        exact differentiableAt_id
      }
      have h12 : deriv (fun y ↦ 1 - y) t = deriv (fun t ↦ 1) t - deriv (fun t ↦ t) t := by {
        exact deriv_sub h10 h11
      }
      rw [h12, h8, h9]
      simp
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
  have haux :
  EqOn (fun t => deriv (fun t ↦ γ.toFun (1 - t)) t / (γ.toFun (1 - t) - z)) (fun t => - deriv γ (1 - t) / (γ (1 - t) - z)) I := by {
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
  have hint : ∫ (x : ℝ) in I, deriv γ (1 - x) / (γ (1 - x) - z) =
    ∫ (x : ℝ) in (0)..1, deriv γ x / (γ x - z) := by {
      have hintaux : ∫ (t : ℝ) in I, deriv γ (1 - t) / (γ (1 - t) - z) =
      ∫ (t : ℝ) in (0)..(1), deriv γ (1 - t) / (γ (1 - t) - z) := by {
        have hI : I = Set.Icc 0 1 := by {
          ext x
          simp
        }
        rw [hI]
        have hI1 : ∫ (t : ℝ) in Set.Icc 0 1, deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z) =
        ∫ (t : ℝ) in Set.Ioc 0 1, deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z) := by{
          apply MeasureTheory.integral_Icc_eq_integral_Ioc}
        rw [hI1, intervalIntegral.integral_of_le]
        exact zero_le_one' ℝ
      }
      rw [hintaux]
      let f := fun t => deriv γ t / (γ t - z)
      have hF : ∫ (t : ℝ) in (0)..1, deriv γ.toFun (1 - t) / (γ.toFun (1 - t) - z) =
      ∫ (t : ℝ) in (0)..1, f (1 - t) := by {
        unfold f
        rfl
      }
      rw [hF]
      have hF1 : ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z) =
      ∫ (t : ℝ) in (0)..1, f t := by {
        unfold f
        rfl
      }
      rw [hF1, intervalIntegral.integral_comp_sub_left f 1]
      simp
  }
  rw [hint]
  have hω : (1 / (2 * ↑π * Complex.I) * ∫ (x : ℝ) in (0)..1, deriv γ.toFun x / (γ.toFun x - z)) = ω z γ := by {
    unfold ω
    have hintaux : ∫ (x : ℝ) in I, deriv γ x / (γ x - z) =
      ∫ x in (0)..(1), deriv γ x / (γ x - z) := by {
        have hI : I = Set.Icc 0 1 := by {
          ext x
          simp
        }
        rw [hI]
        have hI1 : ∫ (x : ℝ) in Set.Icc 0 1, deriv γ.toFun x / (γ.toFun x - z) =
        ∫ (x : ℝ) in Set.Ioc 0 1, deriv γ.toFun x / (γ.toFun x - z) := by{
          apply MeasureTheory.integral_Icc_eq_integral_Ioc}
        rw [hI1, intervalIntegral.integral_of_le]
        exact zero_le_one' ℝ
      }
    rw [hintaux]
  }
  rw [hω, hn]
}
rw [h2]
ring
}
