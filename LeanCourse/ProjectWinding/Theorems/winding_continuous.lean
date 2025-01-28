import LeanCourse.ProjectWinding.Definitions.curves
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.MetricSpace.Pseudo.Defs


open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

lemma hintaux (f : ℝ → ℂ) : 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, f t =
      1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in (0)..1, f t := by {
        have hI : I = Set.Icc 0 1 := by {
          ext x
          simp
        }
        rw [hI]
        have hI1 : ∫ (t : ℝ) in Icc 0 1, f t =
        ∫ (t : ℝ) in Ioc 0 1, f t:= by{
          apply MeasureTheory.integral_Icc_eq_integral_Ioc}
        rw [hI1, intervalIntegral.integral_of_le]
        exact zero_le_one' ℝ
      }


lemma integral_le_const {a z₀ : ℂ} (γ : closed_curve) (h₁ : ∀ t : ℝ, γ.toFun t - a ≠ 0) (h₂ : ∀ t : ℝ, γ.toFun t - z₀ ≠ 0) :
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
    have haux : (fun t => ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖) =
    (fun t => ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖) := by {
      ext1 t
      simp only [norm_mul, norm_div, norm_eq_abs]
      ring
    }
    rw [haux]
  }
  calc
    ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤
    ∫ (t : ℝ) in I, ‖deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
      exact heq
    }
    _ = ∫ (t : ℝ) in I, ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
      exact heq1
    }
    _ ≤ ∫ (t : ℝ) in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
      have haux : (fun (t : I) => ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖) ≤
      (fun (t : I) => C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖) := by {
        intro t
        apply mul_le_mul_of_nonneg_right
        · exact hC t t.2
        · exact norm_nonneg ((a - z₀) / ((γ.toFun ↑t - a) * (γ.toFun ↑t - z₀)))
      }
      have hintaux2 : ∫ (t : ℝ) in I, ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
      ∫ (t : ℝ) in (0)..1, ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
        have hI : I = Set.Icc 0 1 := by {
          ext x
          simp
        }
        rw [hI]
        have hI1 : ∫ (t : ℝ) in Set.Icc 0 1, ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
        ∫ (t : ℝ) in Set.Ioc 0 1, ‖deriv γ.toFun t‖ * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by{
          apply MeasureTheory.integral_Icc_eq_integral_Ioc}
        rw [hI1, intervalIntegral.integral_of_le]
        exact zero_le_one' ℝ
      }

      have hintaux3 : ∫ (t : ℝ) in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
      ∫ (t : ℝ) in (0)..1, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
        have hI : I = Set.Icc 0 1 := by {
          ext x
          simp
        }
        rw [hI]
        have hI1 : ∫ (t : ℝ) in Set.Icc 0 1, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
        ∫ (t : ℝ) in Set.Ioc 0 1, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by{
          apply MeasureTheory.integral_Icc_eq_integral_Ioc}
        rw [hI1, intervalIntegral.integral_of_le]
        exact zero_le_one' ℝ
      }
      rw [hintaux2, hintaux3]
      apply intervalIntegral.integral_mono_on
      · exact zero_le_one' ℝ
      · apply Continuous.intervalIntegrable
        have auxi : (fun u ↦ ‖deriv γ.toFun u‖ * ‖(a - z₀) / ((γ.toFun u - a) * (γ.toFun u - z₀))‖) =
        (fun u ↦ ‖deriv γ.toFun u * (a - z₀) / ((γ.toFun u - a) * (γ.toFun u - z₀))‖) := by {
          ext1 u
          rw [← norm_mul]
          ring_nf
        }
        rw [auxi]
        apply Continuous.norm
        apply Continuous.mul
        · apply Continuous.mul
          · exact closed_curve.Cont_deriv γ
          · exact continuous_const
        · have eq : (fun t => ((γ.toFun t - a) * (γ.toFun t - z₀))⁻¹) =
          (fun t => 1/((γ.toFun t - a) * (γ.toFun t - z₀))) := by {
            ext1 t
            rw [inv_eq_one_div]
          }
          rw [eq]
          apply Continuous.div₀
          · exact continuous_const
          · apply Continuous.mul
            · have h1aux : Continuous γ := by exact closed_curve.Cont γ
              have h2aux : Continuous (fun (_ : ℝ) => a) := by exact continuous_const
              exact Continuous.sub h1aux h2aux
            · have h1aux : Continuous γ := by exact closed_curve.Cont γ
              have h2aux : Continuous (fun (_ : ℝ) => z₀) := by exact continuous_const
              exact Continuous.sub h1aux h2aux
          · intro x
            rw [mul_ne_zero_iff]
            exact ⟨h₁ x, h₂ x⟩

      · apply Continuous.intervalIntegrable
        apply Continuous.mul
        · exact continuous_const
        · apply Continuous.norm
          apply Continuous.div₀
          · exact continuous_const
          · apply Continuous.mul
            · have h1aux : Continuous γ := by exact closed_curve.Cont γ
              have h2aux : Continuous (fun (_ : ℝ) => a) := by exact continuous_const
              exact Continuous.sub h1aux h2aux
            · have h1aux : Continuous γ := by exact closed_curve.Cont γ
              have h2aux : Continuous (fun (_ : ℝ) => z₀) := by exact continuous_const
              exact Continuous.sub h1aux h2aux
          · intro x
            rw [mul_ne_zero_iff]
            exact ⟨h₁ x, h₂ x⟩
      · intro x hx
        let b := ‖(a - z₀) / ((γ.toFun x - a) * (γ.toFun x - z₀))‖
        have hb : ‖(a - z₀) / ((γ.toFun x - a) * (γ.toFun x - z₀))‖ = b := rfl
        rw [hb]
        have hbb : b ≥ 0 := by exact norm_nonneg _
        have haux := hC x hx
        exact mul_le_mul_of_nonneg_right haux hbb
    }
  }

/- The next theorem claims that the index function, the so-called winding number but with non-fixed z, this is:
    fun z => 1/(2*π*i) * ∫ t in I, (deriv γ' t) / (γ t - z)
    is continuous on the two connected components of ℂ \ (γ '' I), which we have labelled as
    interior and exterior of γ.
  -/

theorem ω_continuous (γ : closed_curve)
: ContinuousOn (fun z => 1/(2*Real.pi*Complex.I) *  ∫ t in I, (deriv γ t) / (γ t - z)) ((univ \ (image γ I)) : Set ℂ )  := by {
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  refine ⟨ε, hε, ?_⟩
  intro a ha haz₀
  let d := ⨅ (a : ℂ) (_ : a ∈ γ '' I), dist z₀ a
  have hd : d > 0 := by {
    have hz0 : z₀ ∉ γ '' I := by {
      exact not_mem_of_mem_diff hz₀
    }
    have hI : IsCompact (γ '' I) := by {
      exact IsCompact.image (by exact isCompact_Icc) (by exact closed_curve.Cont γ)
    }
    sorry
  }
  let ε' := min (d/2) (ε/2)
  have hd1 : ∀ w ∈ γ '' I, d ≤ ‖z₀ - w‖ := by {
    intro w hw
    unfold d
    rw [← NormedField.dist_eq]
    sorry
  }
  have hz₀w : ∀ z ∈ Metric.ball z₀ ε', ∀ w ∈ γ '' I, ‖z₀ - w‖ ≤ ‖z₀ - z‖ + ‖z - w‖ := by {
    intro z hz
    exact fun w a ↦ norm_sub_le_norm_sub_add_norm_sub z₀ z w
  }
  have hzwl : ∀ z ∈ Metric.ball z₀ ε', ‖z₀ - z‖ < d/2 := by {
    intro z hz
    sorry
  }
  have hzwl' : ∀ z ∈ Metric.ball z₀ ε, ∀ w ∈ γ '' I, d < d/2 + ‖z - w‖ := by {
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
            ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀))‖ := by {
            have aux : 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I,deriv γ.toFun t / (γ.toFun t - a) -
            1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
            1 / (2 * ↑π * Complex.I) * (∫ (t : ℝ) in I,(deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀))) := by{
              calc
                1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I,deriv γ.toFun t / (γ.toFun t - a) -
                1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
                1 / (2 * ↑π * Complex.I) * (∫ (t : ℝ) in I,deriv γ.toFun t / (γ.toFun t - a) -
                ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) := by {
                  --congr
                  sorry
                  --rw [← mul_sub_left_distrib (1 / (2 * ↑π * Complex.I)) (∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)) (∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀))]
                }
                _ = 1 / (2 * ↑π * Complex.I) * (∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀))) := by {
                  rw [hintaux, hintaux]
                  sorry
                }
            }
            rw [aux]
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
  have hnorm1 : ∃ C, ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤
  ∫ (t : ℝ) in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    sorry
  }
  obtain ⟨C, hC⟩ := hnorm1
  have hnorm2 : ∫ (t : ℝ) in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
  C * ∫ (t : ℝ) in I, ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    exact integral_mul_left C fun a_1 ↦ ‖(a - z₀) / ((γ.toFun a_1 - a) * (γ.toFun a_1 - z₀))‖
  }
  have hn1 :  (fun t => ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖) =
  (fun t => ‖(a - z₀)‖ * ‖1/ ((γ.toFun t - a) * (γ.toFun t - z₀))‖) := by {
    ext1 x
    rw [← norm_mul]
    ring_nf
  }
  have hnorm3 : C * ∫ (t : ℝ) in I, ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
  C * ∫ (t : ℝ) in I, ‖(a - z₀)‖ * ‖1/ ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    rw [hn1]
  }
  have aux0 : ∀ t ∈ I, d ≤ ‖γ t - a‖ := by {
    sorry
  }
  have aux1 : ∀ t ∈ I, d/2 ≤ ‖γ t - z₀‖ := by {
    sorry
  }
  have hnorm4 : ∫ (t : ℝ) in I, ‖(a - z₀)‖ * ‖1/ ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
  ‖(a - z₀)‖ * ∫ (t : ℝ) in I, ‖1/ ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    exact integral_mul_left ‖(a - z₀)‖ $ fun a_1 ↦ ‖1/ ((γ.toFun a_1 - a) * (γ.toFun a_1 - z₀))‖
  }
  rw [hnorm4] at hnorm3
  have prod : ∀ t ∈ I, d * (d/2) ≤ ‖γ t - a‖ * ‖γ t - z₀‖ := by {
    intro x hx
    apply mul_le_mul
    exact aux0 x hx
    exact aux1 x hx
    nlinarith
    exact norm_nonneg $ γ.toFun x - a
  }
  have funless : (fun (t : I) => ‖1 / ((γ.toFun t - a) * (γ.toFun t - z₀))‖) ≤
  (fun (t : I) => 1 / (d * (d/2))) := by {
    intro t
    have haux : (fun (t : I) ↦ ‖1 / ((γ.toFun ↑t - a) * (γ.toFun ↑t - z₀))‖) =
        (fun (t : I) ↦ 1 / (‖(γ.toFun ↑t - a)‖ * ‖(γ.toFun ↑t - z₀)‖)) := by {
          simp only [norm_div, norm_mul]; simp
    }
    rw [haux]
    have ha0 : 0 < ‖γ.toFun ↑t - a‖ := by sorry -- all these should be easy to prove
    have hz₀0 : 0 < ‖γ.toFun ↑t - z₀‖ := by sorry
    have haz : 0 < ‖γ.toFun ↑t - a‖ * ‖γ.toFun ↑t - z₀‖ := by sorry
    have hdd2 : 0 < (d * (d/2)) := by sorry
    rw [div_le_div_iff haz hdd2]
    simp
    apply mul_le_mul
    sorry
    sorry
    sorry
    exact AbsoluteValue.nonneg Complex.abs (γ.toFun ↑t - a)
  }
  sorry
}
