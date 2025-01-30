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
    sorry
  }
  have hz₀w : ∀ z ∈ Metric.ball z₀ ε', ∀ w ∈ γ '' I, ‖z₀ - w‖ ≤ ‖z₀ - z‖ + ‖z - w‖ := by {
    intro z hz
    exact fun w a ↦ norm_sub_le_norm_sub_add_norm_sub z₀ z w
  }
  have hzwl : ∀ z ∈ Metric.ball z₀ ε', ‖z₀ - z‖ < (d/2) := by {
    intro z hz
    sorry
  }
  have hzwl' : ∀ z ∈ Metric.ball z₀ ε, ∀ w ∈ γ '' I, d < (d/2) + ‖z - w‖ := by {
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
                (1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I,deriv γ.toFun t / (γ.toFun t - a)) -
                1 / (2 * ↑π * Complex.I) * ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
                1 / (2 * ↑π * Complex.I) * ((∫ (t : ℝ) in I,deriv γ.toFun t / (γ.toFun t - a) -
                ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀))) := by {
                  rw [← mul_sub_left_distrib (1 / (2 * ↑π * Complex.I)) (∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)) (∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀))]
                  simp
                  left
                  have triv : (∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a)) =
                  ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) := by {
                    rfl
                  }
                  rw [triv]
                  sorry
                }
                _ = 1 / (2 * ↑π * Complex.I) * (∫ (t : ℝ) in I, (deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀))) := by {
                  rw [hintaux] at *
                  have hzoI : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z₀) =
                  ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z₀) := by rw [hintaux1]
                  rw [hzoI, hintaux]
                  have haux : ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
                  ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - a) - ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z₀) := by {
                    sorry
                  }
                  rw [haux]
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

      have haI : ∀ x ∈ I, γ x ≠ z₀ := by {
        intro x hx
        by_contra hcon
        have hain : z₀ ∈ γ '' I := ⟨x, hx, hcon⟩
        exact hz₀notin hain
      }
      have haI1 : ∀ t ∈ I, γ t - z₀ ≠ 0 := by {
        intro x hx
        specialize haI x
        have tri : γ x ≠ z₀ := haI hx
        exact sub_ne_zero_of_ne tri
      }
      specialize haI1 t
      have : γ.toFun t - z₀ ≠ 0 := haI1 ht
      exact this
  }
  have eq2 : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - a) - deriv γ.toFun t / (γ.toFun t - z₀) =
  ∫ (t : ℝ) in I, (deriv γ.toFun t * (a - z₀)) / ((γ.toFun t - a) * (γ.toFun t - z₀)) := by {
    sorry
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
  have hnorm1 : ∃ C, ‖∫ (t : ℝ) in I, deriv γ.toFun t * (a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ ≤
  ∫ (t : ℝ) in I, C * ‖(a - z₀) / ((γ.toFun t - a) * (γ.toFun t - z₀))‖ := by {
    apply integral_le_const
    sorry
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
  have aux1 : ∀ t ∈ I, (d/2) ≤ ‖γ t - z₀‖ := by {
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
