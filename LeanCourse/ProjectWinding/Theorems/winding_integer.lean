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
open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics
open Set unitInterval Finset Metric

noncomputable section

open Classical

lemma exp_one (z : ℂ) (h_1 : Complex.exp z = 1) : ∃ k : ℤ, z = 2 * Real.pi * k * Complex.I := by {
  have h : Complex.exp z = 1 → ∃ n : ℤ , z = n * (2 * ↑π * Complex.I) := by exact Complex.exp_eq_one_iff.1
  have h' : ∃ n : ℤ , z = ↑n * (2 * ↑π * Complex.I) := h h_1
  obtain ⟨ n, hn ⟩ := h'
  use n
  simp[hn]
  ring
  }

-- We are ready to show ω is an integer

theorem ω_integer (γ : closed_curve) (z : ℂ) (h : ∀ t : ℝ , γ t ≠ z)
: ∃ n : ℤ, ω z γ = n := by {
  unfold ω
  have hz : Continuous $ fun s : ℝ  ↦ z := by exact continuous_const
  have hγ : Continuous $ fun s : ℝ ↦ γ s := by exact closed_curve.Cont γ
  let g' := fun s : ℝ ↦ γ s - z
  have hg' : Continuous g' := by {
    unfold g'
    exact Continuous.sub hγ hz
  }
  let g := fun t : ℝ  => ∫ s in (0)..(t), (deriv γ s) / (γ s - z)

  let h' := fun s : ℝ ↦ deriv γ s

  have hh' : Continuous h' := by {
  unfold h'
  suffices h_aux : Continuous $ deriv γ
  · exact h_aux
  · exact closed_curve.Cont_deriv γ
  }

  have h_vanish : ∀ s : ℝ, g' s ≠ 0 := by exact fun s ↦ sub_ne_zero_of_ne $ h s

  let φ := fun s : ℝ ↦ (h' s / g' s)

  have h_cont : Continuous φ := by {
    unfold φ
    exact Continuous.div hh' hg' h_vanish
  }
  have hg'' : ∀ t : ℝ, deriv g t = (deriv γ t) / (γ t - z) := by {
  intro t
  unfold g
  apply Continuous.deriv_integral
  exact h_cont
  }

  let ψ : ℝ → ℂ := fun t ↦ Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * (γ t - z)

  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ (fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) t := by {
              intro t
              simp only [differentiableAt_neg_iff]
              apply DifferentiableOn.differentiableAt
              apply intervalIntegral.differentiableOn_integral_of_continuous
              · exact fun x a ↦ a
              · exact h_cont
              · have h_cont1 : ContinuousOn (fun x ↦ deriv γ x / (γ x - z)) (Set.Ioc 0 t) := by {
                exact Continuous.continuousOn h_cont
              }
                have h_cont2 : ContinuousOn (fun x ↦ deriv γ x / (γ x - z)) (Set.Ioc t 0) := by {
                exact Continuous.continuousOn h_cont
              }
                have h_int1 : IntegrableOn (fun x ↦ deriv γ x / (γ x - z)) (Set.Ioc 0 t) volume := by {
                apply Continuous.integrableOn_Ioc
                exact h_cont
              }
                have h_int2 : IntegrableOn (fun x ↦ deriv γ x / (γ x - z)) (Set.Ioc t 0) volume := by {
                apply Continuous.integrableOn_Ioc
                exact h_cont
              }
                exact Filter.Eventually.of_forall $ fun x =>
                  let h_int1 : IntegrableOn (fun x ↦ deriv γ.toFun x / (γ.toFun x - z)) (Set.Ioc 0 x) volume := by {
                    apply Continuous.integrableOn_Ioc
                    exact h_cont
                  }
                  let h_int2 : IntegrableOn (fun x ↦ deriv γ.toFun x / (γ.toFun x - z)) (Set.Ioc x 0) volume := by {
                    apply Continuous.integrableOn_Ioc
                    exact h_cont
                  }
                  And.intro h_int1 h_int2
               }
  have deriv₀ : ∀ t : ℝ, deriv ψ t = 0 := by {
    intro t
    calc
      deriv ψ t
        = deriv (fun t ↦ Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z))) t * (γ t - z)
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv (fun t ↦ γ t - z) t := by {
          have h₁ : DifferentiableAt ℝ (fun y ↦ γ.toFun y - z) t := by {
            simp_all only [Set.mem_Icc, ne_eq, and_imp, differentiableAt_const,
            DifferentiableAt.sub_iff_left, g', h',
              φ, g]
            have hγdiff : Differentiable ℝ γ.toFun := by exact curve.Diff γ.tocurve
            exact Differentiable.differentiableAt hγdiff
          }
          apply deriv_mul
          · exact DifferentiableAt.cexp $ hdiff t

          · exact h₁
        }
    _ = - Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t / (γ t   - z) * (γ t - z)
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          rw [div_mul_cancel₀
              (-Complex.exp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) *
                deriv γ.toFun t)
              $ h_vanish t]
          simp_all only [ne_eq, Set.mem_Icc, and_imp, neg_mul, neg_add_cancel, g', h', φ, g]
          have heqcal : deriv (fun t ↦ cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z))) t =
          -cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * (deriv γ.toFun t / (γ.toFun t - z)) := by {

            have hstep1 : deriv (fun x ↦ cexp (-∫ (s : ℝ) in (0)..x, deriv γ.toFun s / (γ.toFun s - z))) t =
            cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) *
            deriv (fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) t := by {
              exact deriv_cexp $ hdiff t
            }
            have hstep2 : (fun u ↦ -∫ (x : ℝ) in (0)..u, deriv γ.toFun x / (γ.toFun x - z)) =
            (fun u ↦ ∫ (x : ℝ) in (0)..u, - deriv γ.toFun x / (γ.toFun x - z)) := by {
              ext1 x
              rw [← intervalIntegral.integral_neg]
              have hstep2aux : (fun x => -(deriv γ.toFun x / (γ.toFun x - z))) =
              (fun x => -deriv γ.toFun x / (γ.toFun x - z)) := by {
                ext1 x
                ring
              }
              rw [hstep2aux]
            }
            have hstep3 : deriv (fun u ↦ -∫ (x : ℝ) in (0)..u, deriv γ.toFun x / (γ.toFun x - z)) t =
            - deriv γ.toFun t / (γ.toFun t - z) := by {
              rw [hstep2]
              apply Continuous.deriv_integral
              · exact Continuous.div (Continuous.neg $ closed_curve.Cont_deriv γ) hg' h_vanish
            }
            rw [hstep1]
            rw [hstep3]
            ring
            }
          rw [heqcal]
          simp_all only [ne_eq, Set.mem_Icc, and_imp, neg_mul, neg_add_cancel, g', h', φ, g]
          have div : (deriv γ.toFun t / (γ.toFun t - z)) *
          (γ.toFun t - z) = deriv γ.toFun t := by {
            rw [div_mul_cancel₀ (deriv γ.toFun t) $ h_vanish t]
           }
          have hdivaux : -(cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * (deriv γ.toFun t / (γ.toFun t - z)) *
          (γ.toFun t - z)) +
          cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv (fun t ↦ γ.toFun t - z) t =
          -cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t +
          cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t  := by {
            field_simp
            simp_all only [differentiableAt_neg_iff, deriv_cexp, deriv.neg', mul_neg, neg_inj, mul_eq_mul_left_iff,
              Complex.exp_ne_zero, or_false, isUnit_iff_ne_zero, ne_eq, not_false_eq_true, IsUnit.div_mul_cancel]
            have hequ : -(cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t * (γ.toFun t - z)) / (γ.toFun t - z) +
            cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv (fun t ↦ γ.toFun t - z) t = 0 ↔
             (cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t * (γ.toFun t - z)) / (γ.toFun t - z) =
             cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv (fun t ↦ γ.toFun t - z) t := by {
              constructor
              · intro ht₁
                have his1 : (γ.toFun t - z) / (γ.toFun t - z) = 1:= by {
                  exact div_self $ h_vanish t
                }
                have h_lhs :
                 cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t * (γ.toFun t - z) /
                (γ.toFun t - z) =
                cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t := by
                {simp [mul_div_assoc, his1, mul_one]}
                have h_rhs :
                cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv (fun t ↦ γ.toFun t - z) t =
                cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t := by
                {simp [deriv_sub, deriv_const, sub_zero]; exact deriv_sub_const z}
                rw [h_lhs, h_rhs]

              · intro ht₂
                rw[← ht₂]
                ring
             }
            rw[hequ]
            have hsufeq : cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t * (γ.toFun t - z) / (γ.toFun t - z) = cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t := by {
              exact
                mul_div_cancel_right₀
                  (cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t)
                  $ h_vanish t
            }
            rw[hsufeq]
            have hderiv_γ : deriv γ.toFun t = deriv (fun t ↦ γ.toFun t - z) t := by {
              exact Eq.symm $ deriv_sub_const z
            }
            exact
              congrArg (HMul.hMul $ cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)))
                hderiv_γ

          }
          rw [hdivaux]
          ring
        }
    _ = -Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          rw [div_mul_cancel₀
              (-Complex.exp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) *
                deriv γ.toFun t)
              $ h_vanish t]
        }
    _ = 0 := by ring
    }
  have coincide_ψ : ψ 0 = ψ 1 := by {
    have h_cont : ContinuousOn (fun t ↦ deriv γ.toFun t / (γ.toFun t - z)) I := by {
      apply Continuous.continuousOn
      exact h_cont
    }
    have hcont : ContinuousOn ψ I := by {
      refine ContinuousOn.mul ?_ ?_
      · have hF : ContinuousOn (fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) I := by {
        apply ContinuousOn.neg
        have h_int : IntegrableOn (fun t ↦ deriv γ.toFun t / (γ.toFun t - z)) I := by {
          have hK : IsCompact I := by exact isCompact_Icc
          exact ContinuousOn.integrableOn_compact hK h_cont
        }
        have hI : Set.uIcc 0 1 = I := by {
          refine uIcc_of_le ?_; linarith
        }
        rw [← hI] at h_int
        rw [← hI]
        exact intervalIntegral.continuousOn_primitive_interval h_int
        }
        exact ContinuousOn.cexp hF
      · exact Continuous.continuousOn hg'
    }

    have h_const : ∀ x : ℝ, ψ x = ψ 0 := by {
      intro x
      apply is_const_of_deriv_eq_zero
      · unfold ψ
        have hcomp : (fun t ↦ cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z))) =
        (Complex.exp ∘ fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) := by {
          ext1 t
          simp
        }
        apply Differentiable.mul
        · rw [hcomp]
          apply Differentiable.comp
          · exact Complex.differentiable_exp
          · exact hdiff
        · apply Differentiable.sub
          · exact closed_curve.Diff γ
          · exact differentiable_const z
      · exact deriv₀
    }
    simp_all only [Set.mem_Icc, ne_eq, and_imp, intervalIntegral.integral_same,
    neg_zero, Complex.exp_zero, one_mul,
      le_refl, zero_le_one, g', h', φ, g, ψ]
  }

  simp_rw[ψ] at coincide_ψ
  have hψ₀ : ψ 0 = γ.toFun 0 - z := by {
    have hg_0 : g 0 = 0 := by exact intervalIntegral.integral_same
    have hg__0 : -g 0 = 0 := by simp[hg_0]
    have exp_g : Complex.exp (-g 0) = 1 := by simp[hg__0]
    simp_rw[ψ]
    simp_rw[exp_g]
    simp
  }
  have hψ₁ : ψ 1 = Complex.exp (-g 1) * (γ.toFun 0 - z) := by simp[γ.closed]
  have h_simp : (γ.toFun 0 - z) = Complex.exp (-g 1) * (γ.toFun 0 - z)  := by {
    nth_rewrite 1 [← hψ₀]; rw[← hψ₁]; exact coincide_ψ
  }
  have hexp: Complex.exp (-g 1) = 1 := by {
    have h_dist : γ.toFun 0 ≠ z := by {
      specialize h 0
      exact h
    }
    have h_distinct : γ.toFun 0 - z ≠ 0 := by exact sub_ne_zero_of_ne h_dist
    simp[h_distinct] at h_simp
    exact h_simp
  }
  have h_g : ∃ n : ℤ, -g 1 = 2 * Real.pi * n * Complex.I := by {
    exact exp_one (z := -g 1) (h_1 := hexp)
  }
  simp_rw[g] at *
  have h_minus : ∃ n : ℤ, ∫ (s : ℝ) in (0).. 1, deriv γ.toFun s / (γ.toFun s - z) = 2 * ↑π * ↑n * Complex.I := by {
    obtain ⟨k, hk⟩ := h_g
    use -k
    push_cast
    simp[hk]
    rw[← hk]
    ring
  }
  obtain ⟨m, hm⟩ := h_minus
  -- It suffices to prove the following:
  have hsuff : ∃ n : ℤ, ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = 2 * Real.pi * ↑n * Complex.I := by {
    have h_eq : ∫ (t : ℝ) in I, deriv γ.toFun t / (γ.toFun t - z) = ∫ (t : ℝ) in (0)..1, deriv γ.toFun t / (γ.toFun t - z) := by {
      rw [intervalIntegral.integral_of_le]
      have h': [[0, 1]] = I := by refine uIcc_of_le ?h; linarith
      rw[← h']
      simp[Eq.symm integral_Icc_eq_integral_Ioc]
      linarith
    }
    use m
    simp[h_eq, hm]
    }
  have not_zero : (2 * ↑π * Complex.I) ≠ 0 := by {
    simp
    exact pi_ne_zero
  }
  field_simp[hsuff, not_zero]
  have h_equal : ∀ n : ℤ, (n : ℂ) * (2 * ↑π * Complex.I) = 2 * ↑π * (n : ℂ) * Complex.I := by {
    intro n
    ring
  }
  simp[h_equal]
  exact hsuff
}

#min_imports
