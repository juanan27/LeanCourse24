import LeanCourse.ProjectWinding.Definitions.curves
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.MetricSpace.Pseudo.Defs


open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

lemma integral_le_long {a z₀ : ℂ} (γ : closed_curve) :
 ∃ C, ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤ ∫ t in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
  have hbound : ∃ C, ∀ t ∈ I, ‖deriv γ t‖ ≤ C := by {
    have hγ : ContinuousOn (deriv γ.toFun) I := by
      exact curve.Cont_derivOn γ.tocurve
    have hI : IsCompact I := by
      exact isCompact_Icc
    exact IsCompact.exists_bound_of_continuousOn hI hγ
  }
  obtain ⟨C, hC⟩ := hbound
  use C
  have hintaux : ∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀)) =
      ∫ (t : ℝ) in (0)..1, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀)) := by {
        have hI : I = Set.Icc 0 1 := by {
          ext x
          simp
        }
        rw [hI]
        have hI1 : ∫ (t : ℝ) in Set.Icc 0 1, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀)) =
        ∫ (t : ℝ) in Set.Ioc 0 1, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀)) := by{
          apply MeasureTheory.integral_Icc_eq_integral_Ioc}
        rw [hI1, intervalIntegral.integral_of_le]
        exact zero_le_one' ℝ
      }
  have hintaux1 : ∫ (t : ℝ) in I, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
      ∫ (t : ℝ) in (0)..1, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
        have hI : I = Set.Icc 0 1 := by {
          ext x
          simp
        }
        rw [hI]
        have hI1 : ∫ (t : ℝ) in Set.Icc 0 1, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
        ∫ (t : ℝ) in Set.Ioc 0 1, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by{
          apply MeasureTheory.integral_Icc_eq_integral_Ioc}
        rw [hI1, intervalIntegral.integral_of_le]
        exact zero_le_one' ℝ
      }
  have heq : ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤
  ∫ (t : ℝ) in I, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    rw [hintaux, hintaux1]
    exact intervalIntegral.norm_integral_le_integral_norm (by aesop)
  }
  have heq1 : ∫ (t : ℝ) in I, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
  ∫ (t : ℝ) in I, ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    have haux : ∀ t : ℝ, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
    ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
      intro t
      simp only [norm_mul, norm_div, norm_eq_abs]
      ring
    }
    sorry
  }
  calc
    ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤
    ∫ (t : ℝ) in I, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
      exact heq
    }
    _ = ∫ (t : ℝ) in I, ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
      exact heq1
    }
    _ ≤ ∫ t in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
      sorry
    }
  }

-- The index function is continuous

theorem ω_continuous (γ : closed_curve) (z : ℂ) (h : z ∉ γ '' I)
: ContinuousOn (fun z => 1/(2*Real.pi*Complex.I) *  ∫ t in I, (deriv γ t) / (γ t - z)) ((univ \ (image γ I)) : Set ℂ )  := by {
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  refine ⟨ε, hε, ?_⟩
  intro a ha haz₀
  let d := ⨅ (a : ℂ) (_ : a ∈ γ '' I), dist z₀ a
  have hd : d > 0 := by {
    sorry
  }
  let ε' := min (d/2) (ε/2)
  have hd1 : ∀ w ∈ γ '' I, d ≤ ‖z₀ - w‖ := by {
    intro w hw
    sorry
  }
  have hz₀w : ∀ w ∈ γ '' I, ‖z₀ - w‖ ≤ ‖z₀ - z‖ + ‖z - w‖ := by {
    exact fun w a ↦ norm_sub_le_norm_sub_add_norm_sub z₀ z w
  }
  have hzwl : ‖z₀ - z‖ < d/2 := by {
    sorry
  }
  have hzwl' : ∀ w ∈ γ '' I, d < d/2 + ‖z - w‖ := by {
    sorry
  }
  have eq : dist (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a))
    (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) =
    ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)-
    1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)‖ := by {
      rw [NormedField.dist_eq]
      have triv : (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)) =
      1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) := by {
        rfl
      }
      sorry
    }
  rw [eq]
  have diff : ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I,deriv γ.toFun t / (γ.toFun t - a) -
          1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)‖ =
          ‖1 / (2 * ↑π * Complex.I) *
           ∫ (t : ℝ) in I,
          (deriv γ.toFun t / (γ.toFun t - a) -
           deriv γ.toFun t / (γ.toFun t - z₀))‖ := by {
            sorry
            }
  rw [diff]
  have eq1 : ∀ t ∈ I, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
  (deriv γ.toFun t * (a - z₀)) / ((γ.toFun t - a) * (γ.toFun t - z₀)) := by {
    intro t ht
    rw [div_sub_div]
    have aux : (deriv γ.toFun t * (γ.toFun t - z₀) - (γ.toFun t - a) * deriv γ.toFun t) =
    deriv γ.toFun t * (a - z₀) := by {
      ring
    }
    rw [aux]
    have hanotin : a ∉ γ '' I := by {
      exact not_mem_of_mem_diff ha
    }
    · sorry
    · sorry
  }
  have eq2 : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
  ∫ (t : ℝ) in I, (deriv γ.toFun t * (a - z₀)) / ((γ.toFun t - a) * (γ.toFun t - z₀)) := by {
    sorry
  }
  rw [eq2]
  have hnorm : ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
  1 / (2 * π) * ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    sorry
  }
  rw [hnorm]
  sorry
}
