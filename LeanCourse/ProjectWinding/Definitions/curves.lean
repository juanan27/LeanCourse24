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
import Mathlib.MeasureTheory.Function.Jacobian
open DifferentiableOn Finset
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal

/- In this document we present some basic definitions of the winding number around a point x
Intuitively, for an oriented closed curve γ, we can define it as

w(γ, x) = "number of times γ winds around x"

-/

/- To warm up, we will start with probably one of the most basic definitios of the winding number,
this is, using the Cauchy Integral Formula (from now on, CIF) -/


/- First definitions will be way simpler, but this will escalate quickly! -/

open Set unitInterval Finset Metric

structure curve where
 toFun : ℝ → ℂ
 diff_curve : DifferentiableOn ℝ toFun $ I
 cont_deriv : ContinuousOn (deriv toFun) $ I

-- It is sometimes useful to interpret curves as (ℝ → ℂ) maps
instance : CoeFun curve fun _ => ℝ → ℂ := ⟨fun f => f.toFun⟩

-- We'll make continuity and differentiability of curves explicit using Lemmas

lemma curve.ContOn (γ : curve) : ContinuousOn γ I := by {
  exact DifferentiableOn.continuousOn $ γ.diff_curve
  }


lemma curve.DiffOn (γ : curve) : DifferentiableOn ℝ γ I := by {
  exact γ.diff_curve


}



lemma curve.Cont_derivOn (γ : curve) : ContinuousOn (deriv γ) $ I := by {
  exact γ.cont_deriv
}

-- Let us now define the structure of a closed curve from the definition of curve. It inherits
-- continuity and differentiability

structure closed_curve extends curve where
closed : toFun 0 = toFun 1

-- Closed curves can also be seen as functions, as we've done before

instance : CoeFun (closed_curve) fun _ => ℝ → ℂ := ⟨fun f => f.toFun⟩

-- Let us check this defintion works with the following example

def curve.is_closed {a b : ℝ} (γ : curve) : Prop :=
  γ.toFun a = γ.toFun b

-- To generalize, we can define piecewise curves:

structure piecewiseCurve (n : ℕ) where
  curves : Fin n → curve

-- A curve can be seen as a 1-curve piecewise curve:

instance : Coe curve (piecewiseCurve 1) where
  coe := fun c => {curves := fun 0 => c}

/- Now, we define the concatenation of piecewise curves. If γ is a piecewise curve formed by n curves
 and ψ is a piecewise curve formed by m, the γψ is a piecewise curve with (n + m) curves -/


def concatenationOfCurves {n m : ℕ} (γ : piecewiseCurve n) (ψ : piecewiseCurve m) : piecewiseCurve (n + m) :=
  {curves := fun i => by
    by_cases h : i < n
    · exact γ.curves $ Fin.castLT i h
    · simp_all only [not_lt]
      refine ψ.curves $ Fin.subNat n {
        val := i
        isLt := ?_
      } h
      rw [add_comm m n]
      exact i.isLt
  }

/- Anyways, we will potentially make use of closed_curves. The definition of piecewise curves is given
 in case we need it later -/

-- We give the first def of Winding Number

noncomputable def ω (z : ℂ) (γ : closed_curve) : ℂ :=
              1/(2*Real.pi*Complex.I) *  ∫ t in I, (deriv γ t) / (γ t - z)

-- Now we define the interior and exterior of a curve using the winding number (by a proven lemma, ω is always an integer)

def interiorOfClosedCurve (γ : closed_curve) : Set ℂ := {z : ℂ | ω z γ ≠ 0 ∧ z ∉ γ '' I}

def exteriorOfClosedCurve (γ : closed_curve) : Set ℂ := {z : ℂ | ω z γ = 0 ∧ z ∉ γ '' I}

-- For completeness we also include the definition for the image of a closed curve

def imageOfClosedCurve (γ : closed_curve) : Set ℂ := {z : ℂ | z ∈ γ '' I}
