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

open DifferentiableOn Finset
/- In this document we present some basic definitions of the winding number around a point x
Intuitively, for an oriented closed curve γ, we can define it as

w(γ, x) = "number of times γ winds around x"

-/

/- To warm up, we will start with probably one of the most basic definitios of the winding number,
this is, using the Cauchy Integral Formula (from now on, CIF) -/


/- First definitions will be way simpler, but this will escalate quickly! -/

structure curve (a b : ℝ) where
 toFun : ℝ → ℂ
 diff_curve : DifferentiableOn ℝ toFun $ Set.Icc a b
 cont_deriv : ContinuousOn (deriv toFun) $ Set.Icc a b


-- It is sometimes useful to interpret curves as (ℝ → ℂ) maps
instance {a b : ℝ} : CoeFun (curve a b) fun _ => ℝ → ℂ := ⟨fun f => f.toFun⟩

-- We'll make continuity and differentiability of curves explicit using Lemmas

lemma curve.ContOn {a b : ℝ} (γ : curve a b) : ContinuousOn γ (Set.Icc a b) := by {
  exact DifferentiableOn.continuousOn $ γ.diff_curve
}

lemma curve.DiffOn {a b : ℝ} (γ : curve a b) : DifferentiableOn ℝ γ (Set.Icc a b) := by {
  exact γ.diff_curve
}

-- Let us now define the structure of a closed curve from the definition of curve. It inherits
-- continuity and differentiability

structure closed_curve (a b : ℝ) extends curve a b where
closed : toFun a = toFun b

instance {a b : ℝ} : CoeFun (closed_curve a b) fun _ => ℝ → ℂ := ⟨fun f => f.toFun⟩

-- Let us check this defintion works with the following example

def curve.is_closed {a b : ℝ} (γ : curve a b) : Prop :=
  γ.toFun a = γ.toFun b

noncomputable section

open Classical

-- We give the first def of Winding Number (HAVE TO REFINE THIS)
noncomputable def winding_number_complex {a b : ℝ} (z : ℂ) (γ : closed_curve a b) : ℂ :=
  if ∀ t ∈ Set.Icc a b, γ t ≠ z then
              1/(2*Real.pi*Complex.I) * ∫ t in a..b, (deriv γ t) / (γ t - z)
   else 0

-- TO DO: DEMOSTRAR CON ESTA DEFINICION QUE ES UN ENTERO

-- HAY QUE TRABAJAR EN ESTA PRUEBA; DEFINIR ARGUMENTO (PPAL?)?

theorem winding_number_integer {a b : ℝ} (z : ℂ) (γ : closed_curve a b)
(h : ∀ t ∈ Set.Icc a b, γ t ≠ z) : ∃ (n : ℤ), winding_number_complex z γ = n := by {
  unfold winding_number_complex
  simp [h]
  simp_all only [Set.mem_Icc, ne_eq, and_imp, not_false_eq_true, implies_true, ite_true]
  let Ind := winding_number_complex z γ
  have h_Ind : Ind = winding_number_complex z γ := by exact rfl
  have γ_diff : DifferentiableOn ℝ γ (Set.Icc a b) := by exact curve.DiffOn γ.tocurve
  have γz_diff : DifferentiableOn ℝ (fun t => γ t - z) (Set.Icc a b) := by {
    simp
    exact γ_diff
  }
  have h_log_diff : DifferentiableOn ℝ (fun t => Complex.log (γ t - z)) (Set.Icc a b) := by {
    --simp_all only [differentiableOn_const, sub_iff_left]
    refine add ?hf ?hg
    · have aux : DifferentiableOn ℝ (fun t => Complex.abs (γ t - z)) (Set.Icc a b) := by {
        sorry
      }
      sorry
    · sorry
  }
  have h_log : ∫ t in a..b, deriv γ t / (γ t - z) = Complex.log (γ b - z) - Complex.log (γ a - z) := by sorry
  rw [h_log]
  field_simp
  sorry

}

-- DISCRETE WINDING NUMBER??
