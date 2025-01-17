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

noncomputable section

open Classical

theorem division_continuous (f : ℝ → ℂ ) (g : ℝ → ℂ ) (h : ContinuousOn f (I))
(h' : ContinuousOn g (I)) (h_v : ∀ s ∈ I, g s ≠ 0) : ContinuousOn (fun s ↦ f s / g s) (I) := by {
apply h.div
exact h'
exact fun x a ↦ h_v x a
}

theorem division_continuous_ball (f : ℂ → ℂ ) (g : ℂ → ℂ ) (h : ContinuousOn f (closedBall 0 1))
(h' : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ f s / g s) (closedBall 0 1) := by {
  apply h.div
  exact h'
  exact fun x a ↦ h_v x a}

theorem inverse_continuous_ball (g : ℂ → ℂ)
(h : ContinuousOn g (closedBall 0 1)) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ContinuousOn (fun s ↦ 1 / g s) (closedBall 0 1) := by {
  let f : ℂ → ℂ := fun z ↦ 1
  have hf : ContinuousOn f (closedBall 0 1) := by exact continuousOn_const
  have hquot : ContinuousOn (fun s ↦ f s / g s) (closedBall 0 1) := by exact division_continuous_ball f g hf h h_v
  exact hquot
}
theorem inverse_continuous_ball_2 (g : ℂ → ℂ)
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

theorem division_differentiable (f : ℂ → ℂ ) (g : ℂ → ℂ ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g ) (h₀ : ∀ z, g z ≠ 0):
 Differentiable ℂ (fun s ↦ f s / g s) := by {
  apply hf.div
  trivial
  tauto
 }

theorem inverse_differentiable (g : ℂ → ℂ)
(h : Differentiable ℂ g ) (h_v : ∀ s, g s ≠ 0) : Differentiable ℂ (fun s ↦ 1 / g s)  := by {
let f : ℂ → ℂ := fun z ↦ 1
have hf : Differentiable ℂ f := by exact differentiable_const 1
have hqout : Differentiable ℂ (fun s ↦ 1 / g s) := by exact division_differentiable (fun s ↦ 1) g hf h h_v
exact hqout
}

theorem division_differentiable_ball (f : ℂ → ℂ ) (g : ℂ → ℂ ) (hf : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ f z_1) (hg : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1 ) (h₀ : ∀ z, g z ≠ 0):
 ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ f s / g s) z_1 := by {
  intro z_1 h_z1
  specialize hf z_1 h_z1
  specialize hg z_1 h_z1
  apply hf.div
  · exact hg
  · tauto
 }

theorem inverse_differentiable_ball (g : ℂ → ℂ)
(h : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ 1 / g s) s  := by {
  let f : ℂ → ℂ := fun z ↦ 1
  intro s hs
  have hf : ∀ s ∈ closedBall 0 1, DifferentiableAt  ℂ f s := by exact fun s a ↦ differentiableAt_const 1
  have hquot : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ  (fun s ↦ f s / g s) s := by exact fun s a ↦ DifferentiableAt.div (hf s a) (h s a) (h_v s a)
  exact hquot s hs
  }
theorem inverse_differentiable_ball_2 (g : ℂ → ℂ)
(h : ∀ z_1 ∈ closedBall 0 1, DifferentiableAt ℂ g z_1) (h_v : ∀ s ∈ closedBall 0 1, g s ≠ 0) : ∀ s ∈ closedBall 0 1, DifferentiableAt ℂ (fun s ↦ (g s)⁻¹) s  := by {
  intro s hs
  exact DifferentiableAt.inv (h s hs) (h_v s hs)
}

lemma ftc (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

lemma ftc_2 (f : ℝ → ℂ) (hf : ContinuousOn f (I)) :
      ∀ b ∈ I, deriv (fun u ↦ ∫ x : ℝ in (0)..u, f x) b = f b :=
  by {
    intro b hb
    have h_deriv : HasDerivAt (fun u ↦ ∫ x : ℝ in (0)..u, f x) (f b) b := by {
      have hint : IntervalIntegrable f volume (0) b := by {
        have hI : [[0, b]] ⊆ I := by {
          intro x hx
          obtain ⟨h1, h2⟩ := hx
          simp at *
          obtain ⟨h3, h4⟩ := hb
          obtain hP|hQ := h1
          · obtain h5|h6 := h2
            · have hxx : x ≤ 1 := by exact le_implies_le_of_le_of_le h5 h4 h3
              exact ⟨hP, hxx⟩
            · have hxx : x ≤ 1 := by exact Preorder.le_trans x b 1 h6 h4
              exact ⟨hP, hxx⟩
          · obtain h5|h6 := h2
            · have hxx : 0 ≤ x := by exact Preorder.le_trans 0 b x h3 hQ
              have hxxx : x = 0 := by exact le_antisymm h5 hxx
              rw [hxxx] at hQ
              have hb0 : b = 0 := by exact le_antisymm hQ h3
              have hx1 : x ≤ 1 := by linarith
              exact ⟨hxx, hx1⟩
            · have hxx : 0 ≤ x := by exact Preorder.le_trans 0 b x h3 hQ
              have hx1 : x ≤ 1 := by linarith
              exact ⟨hxx, hx1⟩
        }
        have haux : ContinuousOn f (Set.uIcc 0 b) := by exact ContinuousOn.mono hf hI
        exact ContinuousOn.intervalIntegrable haux
      }
      have hbb : ContinuousAt f b := by {
        sorry
      }
      have hmeas : StronglyMeasurableAtFilter f (nhds b) := by {
        sorry
      }
      exact intervalIntegral.integral_hasDerivAt_right hint hmeas hbb
    }
    exact HasDerivAt.deriv h_deriv
    }


-- We prove now that the winding number is always an integer. We introduce the following lemma:

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
  have hz : Continuous (fun s : ℝ  ↦ z) := by exact continuous_const
  have hγ : Continuous (fun s : ℝ ↦ γ s) := by exact closed_curve.Cont γ
  let g' := fun s : ℝ ↦ γ s - z
  have hg' : Continuous g' := by {
    unfold g'
    exact Continuous.sub hγ hz
  }
  let g := fun t : ℝ  => ∫ s in (0)..(t), (deriv γ s) / (γ s - z)

  let h' := fun s : ℝ ↦ deriv γ s

  have hh' : Continuous h' := by {
  unfold h'
  suffices h_aux : Continuous (deriv γ)
  · exact h_aux
  · exact closed_curve.Cont_deriv γ
  }

  have h_vanish : ∀ s : ℝ, g' s ≠ 0 := by exact fun s ↦ sub_ne_zero_of_ne (h s)

  let φ := fun s : ℝ ↦ (h' s / g' s)

  have h_cont : Continuous φ := by {
    unfold φ
    exact Continuous.div hh' hg' h_vanish
  }
  have hg'' : ∀ t ∈ I, deriv g t = (deriv γ t) / (γ t - z) := by {
  intro t ht
  apply ftc_2
  · sorry
  · exact ht
  }
  let ψ : ℝ → ℂ := fun t ↦ Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * (γ t - z)
  have deriv₀ : ∀ t : ℝ, deriv ψ t = 0 := by {
    intro t
    --have hψ : ψ t = Complex.exp (-g t ) * (γ t - z) := by exact rfl
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
          · have haux : DifferentiableAt ℝ (fun y ↦ - ∫ (s : ℝ) in (0)..y, deriv γ.toFun s / (γ.toFun s - z)) t := by {
            simp_all only [and_imp, differentiableAt_const, DifferentiableAt.sub_iff_left,
              differentiableAt_neg_iff, g', h', φ, g]
            have hintg : ∀ t : ℝ, IntervalIntegrable (fun t => deriv γ.toFun t / (γ.toFun t - z)) MeasureTheory.volume (0) t := by {
              intro t
              apply ContinuousOn.intervalIntegrable
              apply Continuous.continuousOn
              exact h_cont
            }
            apply DifferentiableOn.differentiableAt
            apply intervalIntegral.differentiableOn_integral_of_continuous
            · refine fun x a ↦ hintg x
            · exact h_cont
            · exact univ_mem' hintg
          }
            exact DifferentiableAt.cexp haux

          · exact h₁
        }
    _ = - Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t / (γ t   - z) * (γ t - z)
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          rw [div_mul_cancel₀
              (-Complex.exp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) *
                deriv γ.toFun t)
              (h_vanish t)]
          simp_all only [ne_eq, Set.mem_Icc, and_imp, neg_mul, neg_add_cancel, g', h', φ, g]
          have heqcal : deriv (fun t ↦ cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z))) t =
          -cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * (deriv γ.toFun t / (γ.toFun t - z)) := by {
            have hdiff : DifferentiableAt ℝ (fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) t := by {
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
                exact Filter.Eventually.of_forall (fun x =>
                  let h_int1 : IntegrableOn (fun x ↦ deriv γ.toFun x / (γ.toFun x - z)) (Set.Ioc 0 x) volume := by {
                    apply Continuous.integrableOn_Ioc
                    exact h_cont
                  }
                  let h_int2 : IntegrableOn (fun x ↦ deriv γ.toFun x / (γ.toFun x - z)) (Set.Ioc x 0) volume := by {
                    apply Continuous.integrableOn_Ioc
                    exact h_cont
                  }
                  And.intro h_int1 h_int2)
               }
            have hstep1 : deriv (fun x ↦ cexp (-∫ (s : ℝ) in (0)..x, deriv γ.toFun s / (γ.toFun s - z))) t =
            cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) *
            deriv (fun t ↦ -∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) t := by {
              exact deriv_cexp hdiff
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
              · exact Continuous.div (Continuous.neg (closed_curve.Cont_deriv γ)) hg' h_vanish
            }
            rw [hstep1]
            rw [hstep3]
            ring
            }
          rw [heqcal]
          simp_all only [ne_eq, Set.mem_Icc, and_imp, neg_mul, neg_add_cancel, g', h', φ, g]
          have div : (deriv γ.toFun t / (γ.toFun t - z)) *
          (γ.toFun t - z) = deriv γ.toFun t := by {
            rw [div_mul_cancel₀ (deriv γ.toFun t) (h_vanish t)]
           }
          have hdivaux : -(cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * (deriv γ.toFun t / (γ.toFun t - z)) *
          (γ.toFun t - z)) +
          cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv (fun t ↦ γ.toFun t - z) t =
          -cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t +
          cexp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) * deriv γ.toFun t := by {
            field_simp
            --rw[← div]
            sorry
          }
          rw [hdivaux]
          ring
        }
    _ = -Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t
        + Complex.exp (- ∫ s in (0)..t, deriv γ s / (γ s - z)) * deriv γ t := by {
          rw [div_mul_cancel₀
              (-Complex.exp (-∫ (s : ℝ) in (0)..t, deriv γ.toFun s / (γ.toFun s - z)) *
                deriv γ.toFun t)
              (h_vanish t)]
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
    have hderiv : ∀ t ∈ Set.Ico 0 1, HasDerivWithinAt ψ 0 (Set.Ici t) t := by {
      intro t ht
      have htt : t ∈ I := by exact mem_Icc_of_Ico ht
      have h_deriv : deriv ψ t = 0 := by exact deriv₀ t
      specialize deriv₀ t
      have hmini : HasDerivAt ψ (deriv ψ t) t := by {
        rw [hasDerivAt_iff_tendsto]
        rw [deriv₀]
        simp [mul_zero]
        have eq1 : (fun x' ↦ |x' - t|⁻¹ * Complex.abs (ψ x' - ψ t))
        = (fun x' ↦ Complex.abs (ψ x' - ψ t) * |x' - t|⁻¹) := by {
          ext1 x
          exact CommMonoid.mul_comm |x - t|⁻¹ $ Complex.abs (ψ x - ψ t)
        }
        have eq2 : (fun x' ↦ |x' - t|⁻¹ * Complex.abs (ψ x' - ψ t))
        = (fun x' ↦ Complex.abs (ψ x' - ψ t) / |x' - t|) := by {
          exact eq1
        }
        rw [eq2]
        have hnorm : (fun x => Complex.abs (ψ x - ψ t) / |x - t|) =
        (fun x => Complex.abs ((ψ x - ψ t) / (x- t))) := by {
          ext1 x
          field_simp
          have hn : |x - t| = Complex.abs (x - t) := by {
            have hco : (↑x - ↑t) = ↑(x - t) := by exact rfl
            rw [hco]
            rw [← Complex.abs_ofReal]
            rw [Complex.ofReal_sub]
          }
          rw [hn]
        }
        rw [hnorm]
        simp
        have habs : (fun x ↦ Complex.abs ((ψ x - ψ t) / (↑x - ↑t))) =
        (fun x ↦ ‖(ψ x - ψ t) / (↑x - ↑t)‖) := by {
          ext1 x
          exact rfl
        }
        have hcom : (fun x ↦ Complex.abs ((ψ x - ψ t) / (↑x - ↑t))) =
        (fun x ↦ Complex.abs (ψ x - ψ t) / Complex.abs (↑x - ↑t)) := by {
          ext1 x
          simp_all only [Set.mem_Icc, ne_eq, and_imp, Set.mem_Ico, true_and, map_div₀, norm_div, Complex.norm_eq_abs,
            g', h', φ, g, ψ]
        }
        rw [← hcom, habs]
        --rw [tendsto_zero_iff_norm_tendsto_zero]
        have h_inner : Tendsto (fun x ↦ (ψ x - ψ t) / (↑x - ↑t)) (𝓝 t) (𝓝 0) := by {
          rw [← dslope_same ψ t] at h_deriv
          have eqaux : (fun x ↦ (ψ x - ψ t) / (x - t)) = (fun x => (ψ x - ψ t) * (x - t)⁻¹) := by {
            ext1 x
            rw [div_eq_mul_inv]
            congr
            simp_all only [Set.mem_Icc, ne_eq, and_imp, Set.mem_Ico, true_and, dslope_same,
            map_div₀, ofReal_inv,
              Complex.ofReal_sub, g', h', φ, g, ψ]
          }
          have eqaux1 : (fun x ↦ (ψ x - ψ t) * (x - t)⁻¹) = (fun x => (x - t)⁻¹ * (ψ x - ψ t)) := by {
            ext1 x
            exact CommMonoid.mul_comm (ψ x - ψ t) ↑(x - t)⁻¹
          }
          rw [eqaux, eqaux1]
          have dot : (fun x ↦ ↑(x - t)⁻¹ * (ψ x - ψ t)) = (fun x ↦ ↑(x - t)⁻¹ • (ψ x - ψ t)) := by {
            simp
          }
          rw [dot]

          sorry
        }
        rw [tendsto_zero_iff_norm_tendsto_zero] at h_inner
        exact h_inner
      }
      rw [deriv₀] at hmini
      exact HasDerivAt.hasDerivWithinAt hmini
    }
    have h_const : ∀ x ∈ Set.Icc 0 1, ψ x = ψ 0 := by {
      intro x hx
      exact constant_of_has_deriv_right_zero hcont hderiv x hx
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
  -- It is sufficient to prove the following:
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
  have h_equal : ∀ n : ℤ, (n : ℂ) * (2 * ↑π * Complex.I) = 2 * ↑π * (n:ℂ ) * Complex.I := by {
    intro n
    ring
  }
  simp[h_equal]
  exact hsuff
}
