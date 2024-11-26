import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
  sorry
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
  sorry
  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
  sorry
  }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
  sorry
  }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : sorry := sorry

/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : sorry := sorry



/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G := sorry


/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  sorry
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  sorry
  }


/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact mul_smul g g' x
example (x : X) : (1 : G) • x = x := by exact MulAction.one_smul x

/- Now show that `conjugate` specifies a group action from `G` onto its subgroups. -/
instance : MulAction G (Subgroup G) := sorry



/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := by exact fun x ↦ rfl
    symm := by exact fun {x y} a ↦ id $ Eq.symm a
    trans := by {
      intro x y z hx hy
      simp [hx, hy]
    }
  } -- Here you have to show that this is an equivalence.
                 -- If you click on the `sorry`, a lightbulb will appear to give the fields

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/
def quotient_equiv_subtype (X : Type*) :
    Quotient (myEquivalenceRelation X) ≃ X := {
     toFun := by {
     intro h
     apply Quotient.lift id $ λ a b h => ?_
     repeat exact h
     }
     invFun := by {
     exact fun a ↦ ⟦a⟧
     }
     left_inv := by {
      intro x
      induction x using Quotient.ind; rename_i x
      rfl
     }
     right_inv := by {
      intro x
      rfl
     }
     }


section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  · intro h
    rw [h]
    use (1 : G)
    exact MulAction.one_smul y

  · intro h
    ext a
    constructor
    · intro h'
      obtain ⟨g₁, hy⟩ := h
      obtain ⟨g₂, ha⟩ := h'
      have h₁ : g₁ • x = y := by exact hy
      have h₂ : g₂ • x = a := by exact ha
      use g₂ * g₁⁻¹
      simp
      have hya : (g₂ * g₁⁻¹) • y = a := by {
        calc
           (g₂ * g₁⁻¹) • y = (g₂ * g₁⁻¹) • (g₁ • x) := by rw [h₁]
            _ =  g₂ • (g₁⁻¹ • (g₁ • x)) := by exact mul_smul g₂ g₁⁻¹ (g₁ • x)
            _ = g₂ • x := by rw [@inv_smul_smul]
            _ = a := by rw [h₂]}
      exact hya

    · intro h'
      obtain ⟨g₁, hy⟩ := h
      obtain ⟨g₂, ha⟩ := h'
      have h₁ : g₁ • x = y := by exact hy
      have h₂ : g₂ • y = a := by exact ha
      use g₂ * g₁
      simp
      have hxa : (g₂ * g₁) • x = a := by{
        calc
           (g₂ * g₁) • x = g₂ • (g₁ • x) := by exact mul_smul g₂ g₁ x
           _ = g₂ • y := by rw [h₁]
           _ = a := by rw [h₂]
      }
      exact hxa
  }

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := {g : G | g • x = x}
  mul_mem' := by {
    intro a b ha hb
    have hag : ∃ g1 : G, g1 • a = a := by exact MulAction.exists_smul_eq G a a
    have hbg : ∃ g2 : G, g2 • b = b := by exact MulAction.exists_smul_eq G b b
    obtain ⟨g1, hg1⟩ := hag
    obtain ⟨g2, hg2⟩ := hbg
    have := calc
      (a * b) • x = a • (b • x):= by exact mul_smul a b x
      _= a • x := by exact congrArg (HSMul.hSMul a) hb
      _= x := by exact ha
    trivial
  }
  one_mem' := by simp
  inv_mem' := by {
    simp
    intro x_1 hx_1
    exact inv_smul_eq_iff.mpr $ id $ Eq.symm hx_1
  }

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's prove the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/
def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x :=
by {
  let φ : G ⧸ stabilizerOf G x → orbitOf G x :=
    Quotient.lift
    (fun g => ⟨g • x, by simp only [orbitOf]; simp⟩)
    (by
        intro a b hab
        simp
        refine eq_inv_smul_iff.mp ?_
        simp at hab
        have hr : a⁻¹ • b • x = (a⁻¹ * b) • x := by exact smul_smul a⁻¹ b x
        rw [hr]
        simp [stabilizerOf] at hab
        exact id $ Eq.symm hab
    )
  have h : Bijective φ := by {
  constructor
  · unfold Injective
    apply Quotient.ind
    intro a
    apply Quotient.ind
    intro a1 haa1
    apply Quotient.sound
    simp [stabilizerOf]
    simp_all only [id_eq, Quotient.lift_mk, Subtype.mk.injEq, φ]
    have h2 : x = a⁻¹ • a1 • x := by exact eq_inv_smul_iff.mpr haa1
    have h3 : a⁻¹ • a1 • x = (a⁻¹ * a1) • x := by exact smul_smul a⁻¹ a1 x
    rw[← h3]
    exact id $ Eq.symm h2
  · unfold Surjective
    intro ⟨a, g, h'⟩
    use g
    exact SetCoe.ext h'
  }
  apply Equiv.ofBijective
  exact h
  }



end GroupActions
