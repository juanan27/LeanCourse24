import LeanCourse.ProjectWinding.Definitions.curves
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.MetricSpace.Pseudo.Defs


open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval ENNReal

open Set unitInterval Finset Metric

noncomputable section

open Classical

-- The aim is to show continuity of the index function. Please note that there are a few sorrys
-- left. We believe they might not be so difficult to solve, but the proofs are quite long and messy.

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

lemma hintaux1 (f : ℝ → ℂ) : ∫ (t : ℝ) in I, f t =
      ∫ (t : ℝ) in (0)..1, f t := by {
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


lemma integral_le_const {a z₀ : ℂ} (γ : closed_curve) (h₁ : ∀ t ∈ I, γ.toFun t - a ≠ 0) (h₂ : ∀ t ∈ I, γ.toFun t - z₀ ≠ 0) :
 ∃ C ≥ 0, ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤ ∫ t in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
  have hbound : ∃ C, ∀ t ∈ I, ‖deriv γ t‖ ≤ C := by {
    have hγ : ContinuousOn (deriv γ.toFun) I := by
      exact curve.Cont_derivOn γ.tocurve
    have hI : IsCompact I := by
      exact isCompact_Icc
    exact IsCompact.exists_bound_of_continuousOn hI hγ
  }
  obtain ⟨C, hC⟩ := hbound
  have hC_nonneg : 0 ≤ C := by {
    by_contra hC_neg
    push_neg at hC_neg
    obtain ⟨t, ht⟩ : ∃ t, t ∈ I := by {
      have hI : (0 : ℝ) ∈ I := by exact zero_mem
      use 0
    }
    specialize hC t ht
    have h_contra : ‖deriv γ.toFun t‖ < 0 := lt_of_le_of_lt hC hC_neg
    exact not_lt_of_ge (norm_nonneg _) h_contra
  }
  use C
  use hC_nonneg
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
      · apply ContinuousOn.intervalIntegrable-- cambiar por ContinuousOn!
        have auxi : (fun u ↦ ‖deriv γ.toFun u‖ * ‖(a - z₀) / ((γ.toFun u - a) * (γ.toFun u - z₀))‖) =
        (fun u ↦ ‖deriv γ.toFun u * (a - z₀) / ((γ.toFun u - a) * (γ.toFun u - z₀))‖) := by {
          ext1 u
          rw [← norm_mul]
          ring_nf
        }
        rw [auxi]
        apply ContinuousOn.norm
        apply ContinuousOn.mul
        · apply ContinuousOn.mul
          · have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
            rw [hI]
            exact curve.Cont_derivOn γ.tocurve
          · exact continuousOn_const
        · have eq : (fun t => ((γ.toFun t - a) * (γ.toFun t - z₀))⁻¹) =
          (fun t => 1/((γ.toFun t - a) * (γ.toFun t - z₀))) := by {
            ext1 t
            rw [inv_eq_one_div]
          }
          rw [eq]
          apply ContinuousOn.div₀
          · exact continuousOn_const
          · apply ContinuousOn.mul
            · have h1aux : ContinuousOn γ I := by {
                exact closed_curve.ContOn γ
              }
              have h2aux : ContinuousOn (fun (_ : ℝ) => a) I := by exact continuousOn_const
              have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
              rw [← hI] at h1aux h2aux
              exact ContinuousOn.sub h1aux h2aux
            · have h1aux : ContinuousOn γ I := by {
                exact closed_curve.ContOn γ
              }
              have h2aux : ContinuousOn (fun (_ : ℝ) => z₀) I := by exact continuousOn_const
              have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
              rw [← hI] at h1aux h2aux
              exact ContinuousOn.sub h1aux h2aux
          · intro x hx
            rw [mul_ne_zero_iff]
            have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
            rw [hI] at hx
            exact ⟨h₁ x hx, h₂ x hx⟩

      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.mul
        · exact continuousOn_const
        · apply ContinuousOn.norm
          apply ContinuousOn.div₀
          · exact continuousOn_const
          · apply ContinuousOn.mul
            · have h1aux : ContinuousOn γ I := by {
                exact closed_curve.ContOn γ
              }
              have h2aux : ContinuousOn (fun (_ : ℝ) => a) I := by exact continuousOn_const
              have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
              rw [← hI] at h1aux h2aux
              exact ContinuousOn.sub h1aux h2aux
            · have h1aux : ContinuousOn γ I := by {
                exact closed_curve.ContOn γ
              }
              have h2aux : ContinuousOn (fun (_ : ℝ) => z₀) I := by exact continuousOn_const
              have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
              rw [← hI] at h1aux h2aux
              exact ContinuousOn.sub h1aux h2aux
          · intro x hx
            rw [mul_ne_zero_iff]
            have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
            rw [hI] at hx
            exact ⟨h₁ x hx, h₂ x hx⟩

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

--------------------------------------------------------------------------------------------

lemma integral_I_eq_set (f : ℝ → ℂ)
: ∫ (t : ℝ) in I, f t = ∫ (t : ℝ) in (0)..1, f t := by {
  rw [intervalIntegral.integral_of_le]
  have h': [[0, 1]] = I := by refine uIcc_of_le ?h; linarith
  rw[← h']
  simp[Eq.symm integral_Icc_eq_integral_Ioc]
  linarith
}

theorem ω_continuous (γ : closed_curve)
: ContinuousOn (fun z => 1/(2*Real.pi*Complex.I) * ∫ t in I, (deriv γ t) / (γ t - z)) ((univ \ (image γ I)) : Set ℂ ) := by {
  rw [Metric.continuousOn_iff]
  intro z₀ hz₀ ε hε
  refine ⟨ε, hε, ?_⟩
  intro a ha haz₀
  let d := Metric.infDist z₀ (γ '' I)
  have hd : d > 0 := by {
    have hz0 : z₀ ∉ γ '' I := by {
      exact not_mem_of_mem_diff hz₀
    }
    have hI : IsCompact (γ '' I) := by {
      exact IsCompact.image (by exact isCompact_Icc) (by exact closed_curve.Cont γ)
    }
    unfold d
    have hIclo : IsClosed (γ '' I) := by {
      exact IsCompact.isClosed hI
    }
    have hInonemp : Set.Nonempty (γ '' I) := by {
      exact nonempty_of_nonempty_subtype
    }
    have haux : z₀ ∉ (γ '' I) ↔ 0 < Metric.infDist z₀ (γ '' I) := by {
      exact IsClosed.not_mem_iff_infDist_pos hIclo hInonemp
    }
    have := haux.1 hz0
    exact this
  }

  let ε' := min (d/2) (ε/2)
  have hd1 : ∀ w ∈ γ '' I, d ≤ ‖z₀ - w‖ := by {
    intro w hw
    unfold d
    rw [← NormedField.dist_eq]
    exact Metric.infDist_le_dist_of_mem hw
  }

  have hz₀w : ∀ z ∈ Metric.ball z₀ ε', ∀ w ∈ γ '' I, ‖z₀ - w‖ ≤ ‖z₀ - z‖ + ‖z - w‖ := by {
    intro z hz
    exact fun w a ↦ norm_sub_le_norm_sub_add_norm_sub z₀ z w
  }

  have hzwl : ∀ z ∈ Metric.ball z₀ ε', ‖z₀ - z‖ < (d/2) := by {
    intro z hz
    have hz_dist : dist z z₀ < ε' := mem_ball.mp hz
    rw [NormedField.dist_eq] at hz_dist
    have triv : ‖z - z₀‖ = ‖z₀ - z‖ := by exact norm_sub_rev z z₀
    rw [triv] at hz_dist
    have hε'_le : ε' ≤ d / 2 := min_le_left (d / 2) (ε / 2)
    nlinarith
  }

  have hzwl' : ∀ z ∈ Metric.ball z₀ ε', ∀ w ∈ γ '' I, d < (d/2) + ‖z - w‖ := by {
    intro z hz w hw
    have hd_le : d ≤ ‖z₀ - w‖ := hd1 w hw
    have hz₀w_le : ‖z₀ - w‖ ≤ ‖z₀ - z‖ + ‖z - w‖ := hz₀w z ?_ w hw
    have hz₀z_lt : ‖z₀ - z‖ < d / 2 := hzwl z ?_
    exact lt_of_le_of_lt (le_trans hd_le hz₀w_le) (add_lt_add_right hz₀z_lt ‖z - w‖)
    · have hz_dist : ‖z₀ - z‖ < ε' := by {
      rw [← NormedField.dist_eq]
      apply mem_ball.mp
      rw [Metric.mem_ball_comm] at hz
      exact hz
      }
      have hε'_le : ε' ≤ ε / 2 := min_le_right (d / 2) (ε / 2)
      have hε'_lt : ε' < ε := lt_of_le_of_lt hε'_le (half_lt_self hε)
      exact mem_ball.mpr (lt_of_lt_of_le hz (by linarith))
    · exact hz
  }

  have eq : dist (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a))
    (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) =
    ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a)) -
    1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - z₀))‖ := by {
      rw [NormedField.dist_eq]
      have triv : (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a))) =
      1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a)) := by {
        rfl
      }
      have haux : (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)) -
      1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
      1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)
      - 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) := by {
        refine Eq.symm (eq_sub_iff_add_eq'.mpr ?_)

        have haux₁ : (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) + 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) - 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
        ((1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) - 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀))  + 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) := by {
          have aux1 : (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) + 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) - 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
          1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) := by {
            sorry
          }
          rw [aux1]
          sorry -- really easy but cannot find the way.
        }
        rw[haux₁]
        have haux₂ : ((1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) - 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀)) = 0 := by ring
        rw[haux₂]
        norm_num
      }
      rw [haux]
    }

  rw [eq]
  have diff : ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a)) -
            1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - z₀))‖ =
            ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀))‖ := by {
            have aux : 1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I,(deriv γ.toFun t / (γ.toFun t - a)) -
            1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - z₀)) =
            1 / (2 * ↑π * Complex.I) * (∫ (t : ℝ) in I,(deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀))) := by{

              have := calc
                (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I,(deriv γ.toFun t / (γ.toFun t - a))) -
                1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
                1 / (2 * ↑π * Complex.I) * ((∫ (t : ℝ) in I,deriv γ.toFun t / (γ.toFun t - a) -
                ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀))) := by {
                  rw [← mul_sub_left_distrib (1 / (2 * ↑π * Complex.I)) (∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)) (∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀))]
                  simp
                  left
                  refine sub_eq_iff_eq_add.mpr ?h.a
                  sorry -- should also be easy
                }
                _ = 1 / (2 * ↑π * Complex.I) * (∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀))) := by {
                  rw [hintaux] at *
                  have hzoI : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
                  ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z₀) := by rw [hintaux1]
                  rw [hzoI, hintaux]
                  have haux : ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
                  ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - a) - ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z₀) := by {
                    let f := fun t => deriv γ.toFun t / (γ.toFun t - a)
                    let g := fun t => deriv γ.toFun t / (γ.toFun t - z₀)
                    have hf : f = (fun t => deriv γ.toFun t / (γ.toFun t - a)) := by exact rfl
                    have hg : g = (fun t => deriv γ.toFun t / (γ.toFun t - z₀)) := by exact rfl
                    have hfg : f - g = (fun t => deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀)) := by exact rfl
                    have auxintf : ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - a) =
                    ∫ (t : ℝ) in (0)..1, (f t) := by simp only [hf]
                    have auxintg : ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z₀) =
                    ∫ (t : ℝ) in (0)..1, (g t) := by simp only [hg]
                    have auxintfg : ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
                    ∫ (t : ℝ) in (0)..1, ((f - g) t) := by simp only [hfg]
                    have auxintfg1 : ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - a) - ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z₀) =
                    ∫ (t : ℝ) in (0)..1, (f t) - ∫ (t : ℝ) in (0)..1, (g t) := by simp only [hf, hg]
                    have triv : ∫ (t : ℝ) in (0)..1, ((f - g) t)  = ∫ (t : ℝ) in (0)..1, f t - g t := by {
                      have aux : (fun t => (f - g) t) = (fun t => f t - g t) := by {
                        ext1 t
                        exact rfl
                      }
                      rw [aux]
                    }
                    rw [auxintfg, auxintfg1]
                    rw [triv]
                    have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
                    have hfint : IntervalIntegrable f volume 0 1 := by {
                      rw [hf]
                      apply ContinuousOn.intervalIntegrable
                      apply ContinuousOn.div₀
                      · rw [hI]
                        exact curve.Cont_derivOn γ.tocurve
                      · rw [hI]
                        have h1 : ContinuousOn γ I := by exact closed_curve.ContOn γ
                        have h2 : ContinuousOn (fun _ => a) I := by exact continuousOn_const
                        exact ContinuousOn.sub h1 h2
                      · rw [hI]
                        intro x hx
                        have hanotin : a ∉ γ '' I := by {
                        exact not_mem_of_mem_diff ha
                       }
                        have haI : ∀ x ∈ I, γ x ≠ a := by {
                        intro x hx
                        by_contra hcon
                        have hain : a ∈ γ '' I := ⟨x, hx, hcon⟩
                        exact hanotin hain
                       }
                        have haI1 : ∀ t ∈ I, γ t - a ≠ 0 := by {
                        intro x hx
                        specialize haI x
                        have tri : γ x ≠ a := haI hx
                        exact sub_ne_zero_of_ne tri
                       }
                        specialize haI1 x hx
                        exact haI1
                    }
                    have hgint : IntervalIntegrable g volume 0 1 := by {
                      rw [hg]
                      apply ContinuousOn.intervalIntegrable
                      apply ContinuousOn.div₀
                      · rw [hI]
                        exact curve.Cont_derivOn γ.tocurve
                      · rw [hI]
                        have h1 : ContinuousOn γ I := by exact closed_curve.ContOn γ
                        have h2 : ContinuousOn (fun _ => z₀) I := by exact continuousOn_const
                        exact ContinuousOn.sub h1 h2
                      · rw [hI]
                        intro x hx
                        have hanotin : z₀ ∉ γ '' I := by {
                        exact not_mem_of_mem_diff hz₀
                       }
                        have haI : ∀ x ∈ I, γ x ≠ z₀ := by {
                        intro x hx
                        by_contra hcon
                        have hain : z₀ ∈ γ '' I := ⟨x, hx, hcon⟩
                        exact hanotin hain
                       }
                        have haI1 : ∀ t ∈ I, γ t - z₀ ≠ 0 := by {
                        intro x hx
                        specialize haI x
                        have tri : γ x ≠ z₀ := haI hx
                        exact sub_ne_zero_of_ne tri
                       }
                        specialize haI1 x hx
                        exact haI1
                    }
                    rw [intervalIntegral.integral_sub hfint hgint]
                    field_simp
                  }
                  rw [haux]
                }
              sorry -- should be "direct"
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

    · have haI : ∀ x ∈ I, γ x ≠ a := by {
        intro x hx
        by_contra hcon
        have hain : a ∈ γ '' I := ⟨x, hx, hcon⟩
        exact hanotin hain
      }
      have haI1 : ∀ t ∈ I, γ t - a ≠ 0 := by {
        intro x hx
        specialize haI x
        have tri : γ x ≠ a := haI hx
        exact sub_ne_zero_of_ne tri
      }
      specialize haI1 t
      have : γ.toFun t - a ≠ 0 := haI1 ht
      exact this

    · have hz₀notin : z₀ ∉ γ '' I := by {
      exact not_mem_of_mem_diff hz₀
     }

      have hz0I : ∀ x ∈ I, γ x ≠ z₀ := by {
        intro x hx
        by_contra hcon
        have hain : z₀ ∈ γ '' I := ⟨x, hx, hcon⟩
        exact hz₀notin hain
      }
      have hz0I1 : ∀ t ∈ I, γ t - z₀ ≠ 0 := by {
        intro x hx
        specialize hz0I x
        have tri : γ x ≠ z₀ := hz0I hx
        exact sub_ne_zero_of_ne tri
      }
      specialize hz0I1 t
      have : γ.toFun t - z₀ ≠ 0 := hz0I1 ht
      exact this
  }
  have eq2 : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
  ∫ (t : ℝ) in I, (deriv γ.toFun t * (a - z₀)) / ((γ.toFun t - a) * (γ.toFun t - z₀)) := by {
    let f := fun t => deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀)
    let g := fun t => deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))
    have hf : f = (fun t => deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀)) := by exact rfl
    have hg : g = (fun t => deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))) := by exact rfl
    have auxintf : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
    ∫ (t : ℝ) in I, (f t) := by simp only [hf]
    have auxintg : ∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀)) =
    ∫ (t : ℝ) in I, (g t) := by simp only [hg]
    rw [auxintf, auxintg]
    rw [hintaux1]
    rw [hintaux1]
    apply intervalIntegral.integral_congr
    have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
    rw [hI]
    unfold f g
    exact eq1
  }
  rw [eq2]
  have hnorm : ‖1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
  1 / (2 * π) * ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    rw [norm_mul]
    simp
    left
    exact pi_nonneg
  }
  rw [hnorm]
  have aux0 : ∀ t ∈ I, d ≤ ‖γ t - a‖ := by {
    intro t ht
    have haI : a ∉ γ '' I := by exact not_mem_of_mem_diff ha
    unfold d
    have htt : γ t ∈ γ '' I := by exact Set.mem_image_of_mem γ.toFun ht
    rw [← NormedField.dist_eq]
    sorry
  }
  have aux1 : ∀ t ∈ I, (d/2) ≤ ‖γ t - z₀‖ := by {
    intro t ht
    have htt : γ t ∈ γ '' I := by exact Set.mem_image_of_mem γ.toFun ht
    rw [norm_sub_rev]
    have hzd : d ≤ ‖z₀ - γ t‖ := by {
      unfold d
      exact Metric.infDist_le_dist_of_mem htt
    }
    have hdd2 : (d/2) ≤ d := by {
      field_simp
      exact infDist_nonneg
    }
    exact le_trans hdd2 hzd
  }
  have prod : ∀ t ∈ I, d * (d/2) ≤ ‖γ t - a‖ * ‖γ t - z₀‖ := by {
    intro x hx
    apply mul_le_mul
    exact aux0 x hx
    exact aux1 x hx
    nlinarith
    exact norm_nonneg $ γ.toFun x - a
  }
  have funless : ∀ t ∈ I, (fun (t : I) => ‖1 / ((γ.toFun t - a) * (γ.toFun t - z₀))‖) ≤
  (fun (t : I) => 1 / (d * (d/2))) := by {
    intro t ht
    have haux : ∀ t ∈ I, (fun (t : I) ↦ ‖1 / ((γ.toFun ↑t - a) * (γ.toFun ↑t - z₀))‖) =
        (fun (t : I) ↦ 1 / (‖(γ.toFun ↑t - a)‖ * ‖(γ.toFun ↑t - z₀)‖)) := by {
          intro t
          simp only [norm_div, norm_mul]; simp
    }
    rw [haux]
    have ha0 : ∀ t ∈ I, 0 < ‖γ.toFun ↑t - a‖ := by {
      have haI : a ∉ γ '' I := by exact not_mem_of_mem_diff ha
      intro t ht
      rw [← NormedField.dist_eq]
      have htt : γ t ∈ γ '' I := by exact Set.mem_image_of_mem γ.toFun ht
      have h_ne : γ.toFun t ≠ a := by {
        intro h
        rw [h] at htt
        exact haI htt
      }
      exact dist_pos.mpr h_ne
    }
    have hz₀0 : ∀ t ∈ I, 0 < ‖γ.toFun ↑t - z₀‖ := by {
      have hz0I : z₀ ∉ γ '' I := by exact not_mem_of_mem_diff hz₀
      intro t ht
      rw [← NormedField.dist_eq]
      have htt : γ t ∈ γ '' I := by exact Set.mem_image_of_mem γ.toFun ht
      have h_ne : γ.toFun t ≠ z₀ := by {
        intro h
        rw [h] at htt
        exact hz0I htt
      }
      exact dist_pos.mpr h_ne
    }
    have haz : ∀ t ∈ I, 0 < ‖γ.toFun ↑t - a‖ * ‖γ.toFun ↑t - z₀‖ := by {
      intro t ht
      specialize ha0 t ht
      specialize hz₀0 t ht
      exact mul_pos ha0 hz₀0
      }
    have hdd2 : 0 < (d * (d/2)) := by {
      have hd2pos : 0 < (d/2) := by exact div_pos hd (by exact zero_lt_two)
      exact mul_pos hd hd2pos
    }

    have hdd2' : 0 ≤ (d * (d/2)) := by {
      have hd2pos : 0 < (d/2) ∨ 0 = (d/2) := by {
        left
        exact div_pos hd (by exact zero_lt_two)
        }
      have hdpos : 0 ≤ d := by exact infDist_nonneg
      have hd2pos' : 0 ≤ (d/2) := by exact le_of_lt_or_eq hd2pos
      exact Left.mul_nonneg hdpos hd2pos'
    }

    · intro x
      rw [div_le_div_iff]
      simp
      have hxI : x.val ∈ I := by exact x.property
      specialize prod x
      exact prod hxI
      · specialize haz x
        have hxI : x.val ∈ I := by exact x.property
        exact haz hxI
      · exact hdd2

    · exact t
    · exact ht
  }
  have hic : ∃ C ≥ 0, ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤
  ∫ t in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    apply integral_le_const
    · intro t ht
      have haI : a ∉ γ '' I := by exact not_mem_of_mem_diff ha
      have htt : γ t ∈ γ '' I := by exact Set.mem_image_of_mem γ.toFun ht
      have h_ne : γ.toFun t ≠ a := by {
        intro h
        rw [h] at htt
        exact haI htt
      }
      intro h
      rw [sub_eq_zero] at h
      exact h_ne h
    · intro t ht
      have hz0I : z₀ ∉ γ '' I := by exact not_mem_of_mem_diff hz₀
      have htt : γ t ∈ γ '' I := by exact Set.mem_image_of_mem γ.toFun ht
      have h_ne : γ.toFun t ≠ z₀ := by {
        intro h
        rw [h] at htt
        exact hz0I htt
      }
      intro h
      rw [sub_eq_zero] at h
      exact h_ne h
  }
  obtain ⟨C, hC⟩ := hic
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
  rw [hnorm3] at hnorm2
  have hIcc : I = Set.Icc 0 1 := by exact rfl
  have hI_eq : ∀ t ∈ I, ∫ (t : ℝ) in I, ‖(a - z₀)‖ * ‖1/ ((γ.toFun t - a) * (γ.toFun t - z₀))‖ =
    ∫ (t : ℝ) in (0)..1, ‖(a - z₀)‖ * ‖1/ ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by{
    intro t ht
    rw [hIcc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by exact zero_le_one' ℝ)]
    }
  rw [hI_eq] at hnorm2
  rw [intervalIntegral.integral_const_mul] at hnorm2
  have step : C * (‖a - z₀‖ * ∫ (x : ℝ) in (0)..1, ‖1 / ((γ.toFun x - a) * (γ.toFun x - z₀))‖) =
  C * ‖a - z₀‖ * ∫ (x : ℝ) in (0)..1, ‖1 / ((γ.toFun x - a) * (γ.toFun x - z₀))‖ := by {
    simp
    ring
  }
  rw [step] at hnorm2
  have midstep : ∫ (x : ℝ) in (0)..1, ‖1 / ((γ.toFun x - a) * (γ.toFun x - z₀))‖ ≤
  ∫ (x : ℝ) in (0)..1, 1 / (d * (d / 2)) := by {
    apply intervalIntegral.integral_mono_on
    · exact zero_le_one' ℝ
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.norm
      apply ContinuousOn.div₀
      · exact continuousOn_const
      · apply ContinuousOn.mul
        have hacon : ContinuousOn (fun x => a) [[0, 1]] := by exact continuousOn_const
        have haux : ContinuousOn γ [[0, 1]] := by {
           have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
           rw [hI]
           exact closed_curve.ContOn γ
         }
        · sorry
        · sorry

      · intro x hx
        rw [mul_ne_zero_iff]
        have hI : [[0, 1]] = I := Set.uIcc_of_le zero_le_one
        rw [hI] at hx
        have hz0 : γ.toFun x - z₀ ≠ 0 := by {
        have hz₀notin : z₀ ∉ γ '' I := by {
        exact not_mem_of_mem_diff hz₀
       }

        have haI : ∀ x ∈ I, γ x ≠ z₀ := by {
        intro x hx
        by_contra hcon
        have hain : z₀ ∈ γ '' I := ⟨x, hx, hcon⟩
        exact hz₀notin hain
       }
        have haI1 : ∀ x ∈ I, γ x - z₀ ≠ 0 := by {
        intro x hx
        specialize haI x
        have tri : γ x ≠ z₀ := haI hx
        exact sub_ne_zero_of_ne tri
       }
        specialize haI1 x
        have : γ.toFun x - z₀ ≠ 0 := haI1 hx
        exact this}
        ---------------------------------------
        have han0 : γ.toFun x - a ≠ 0 := by {
        have hanotin : a ∉ γ '' I := by {
        exact not_mem_of_mem_diff ha
        }

        have haI : ∀ x ∈ I, γ x ≠ a := by {
        intro x hx
        by_contra hcon
        have hain : a ∈ γ '' I := ⟨x, hx, hcon⟩
        exact hanotin hain
       }
        have haI1 : ∀ x ∈ I, γ x - a ≠ 0 := by {
        intro x hx
        specialize haI x
        have tri : γ x ≠ a := haI hx
        exact sub_ne_zero_of_ne tri
       }
        specialize haI1 x
        have : γ.toFun x - a ≠ 0 := haI1 hx
        exact this}
        exact Decidable.not_imp_iff_and_not.mp fun a ↦ hz0 (a han0)

    · exact intervalIntegrable_const
    · intro t ht
      specialize funless t ht
      exact funless ⟨t, ht⟩
  }
  have midstep1 : C * ‖a - z₀‖ * ∫ (x : ℝ) in (0)..1, ‖1 / ((γ.toFun x - a) * (γ.toFun x - z₀))‖ ≤
  C * ‖a - z₀‖ * ∫ (x : ℝ) in (0)..1, 1 / (d * (d / 2)) := by {
    apply mul_le_mul
    · exact le_rfl
    · exact midstep
    · apply intervalIntegral.integral_nonneg_of_forall
      · exact zero_le_one' ℝ
      · intro u
        exact norm_nonneg (1 / ((γ.toFun u - a) * (γ.toFun u - z₀)))
    · apply mul_nonneg
      · exact hC.1
      · exact norm_nonneg (a - z₀)
  }
  have eqaux : C * ‖a - z₀‖ * ∫ (x : ℝ) in (0)..1, 1 / (d * (d / 2)) =
  C * ‖a - z₀‖ * 1 / (d * (d / 2)) * 1 := by {
    field_simp
  }
  have triv : C * ‖a - z₀‖ * 1 / (d * (d / 2)) * 1 =
  (C * ‖a - z₀‖) / (d * (d / 2)) := by field_simp

  have C_ge_0 : 0 ≤ C := by {
    exact hC.1
  }
  have auxx : C * ‖a - z₀‖ / (d * (d / 2)) = ‖a - z₀‖ * (C / (d * (d / 2))) := by ring
  rw [auxx] at triv
  rw [NormedField.dist_eq] at haz₀
  have midstep2 : ‖a - z₀‖ * (C / (d * (d / 2))) < ε * (C / (d * (d / 2))) := by {
    sorry
  }
  · sorry -- Using everything from above should not be hard to finish.
  · exact ε
  · refine Set.mem_Icc.mpr ?intro.a.a
    constructor
    · positivity
    · sorry -- epsilon can always be taken smaller than 1.
}
