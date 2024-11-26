import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 2, 3, 4 and 5
  Read chapter 3, sections 1, 4.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 22.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by {
  linarith
  }

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
  --vhave h2 : (u + 1)^2 = v^2 := by rw [h1]
  have h2 : (u + 1)^2 + v - 1 = u^2 + 3*u + 1 := by linarith
  rw [h1] at h2
  symm at h2
  assumption
  }

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by {
    have h4 : a ≤ c := by linarith
    have h5 : exp x ≤ exp y := by linarith [exp_le_exp.mpr h3]
    have h6 : exp y ≤ exp (y + 2) := by simp_all only [exp_le_exp, le_add_iff_nonneg_right, Nat.ofNat_nonneg]
    linarith
  }

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by {
  constructor
  · intro (hab)
    linarith
  · intro (hab1)
    linarith
  }

/- Note: for purely numerical problems, you can use `norm_num`
(although `ring` or `linarith` also work in some cases). -/
example : 2 + 3 * 4 + 5 ^ 6 ≤ 7 ^ 8 := by norm_num
example (x : ℝ) : (1 + 1) * x + (7 ^ 2 - 35 + 1) = 2 * x + 15 := by norm_num

/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example (x : ℝ) (hx : x = 3) : x ^ 2 + 3 * x - 5 = 13 := by
  rw [hx]
  norm_num

example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by {
  have h : 0 ≤ m^2 := by exact sq_nonneg m
  have h1 : n - m^2 ≤ n := by linarith
  simp
  linarith
  }

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by {
have h1 : ∀ b : ℝ, -3 + 4 * b - b ^ 2 = - (b - 2)^2 + 1 := by
    intro b
    ring
have h2 : ∀ b : ℝ, a ≥ - (b - 2)^2 + 1 := by
    intro b
    rw [← h1 b]
    exact h b
-- mirar bien esto por si se puede hacer más fácil
specialize h2 2
linarith
  }

example {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁₂ : a₁ + a₂ + 1 ≤ b₁ + b₂) (h₃ : a₃ + 2 ≤ b₃) :
  exp (a₁ + a₂) + a₃ + 1 ≤ exp (b₁ + b₂) + b₃ + 1 := by {
  sorry
  }


/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

/-- Prove this using calc. -/
lemma exercise_division (n m k l : ℕ) (h₁ : n ∣ m) (h₂ : m = k) (h₃ : k ∣ l) : n ∣ l := by {
  sorry
  }


/- We can also work with abstract partial orders. -/

section PartialOrder

variable {X : Type*} [PartialOrder X]
variable (x y z : X)

/- A partial order is defined to be an order relation `≤` with the following axioms -/
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

/- every preorder comes automatically with an associated strict order -/
example : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

/- the reverse order `≥`/`>` is defined from `≤`/`<`.
In Mathlib we usually state lemmas using `≤`/`<` instead of `≥`/`>`. -/
example : x ≥ y ↔ y ≤ x := by rfl
example : x > y ↔ y < x := by rfl


example (hxy : x ≤ y) (hyz : y ≤ z) (hzx : z ≤ x) : x = y ∧ y = z ∧ x = z := by {
  sorry
  }


end PartialOrder


/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  calc t ^ 2 - 3 * t - 17 = t * (t - 3) - 17 := by ring
      _ ≥ 10 * (10 - 3) - 17 := by gcongr
      _ = 53 := by ring
      _ ≥ 5 := by linarith
}
/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = t ^ 2 * t ^ 2 + 3 * t ^ 2 * t - 3 * t ^ 2- 2 * t - 2
    := by ring
    _ = 4 * 4 + 3 * 4 * t - 3 * 4 - 2 * t - 2 := by congr; repeat (simp_rw [sub_eq_zero] at ht; assumption)
ring
  }


/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  calc
      n + 1 ≤ 3 - m ^ 2 := by linarith
      _ ≤ 3 := by simp_all only [tsub_le_iff_right, le_add_iff_nonneg_right]; apply sq_nonneg m
      _ ≤ 3 + k ^ 2 := by simp_all only [le_add_iff_nonneg_right, sq_nonneg k]
  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize `min`.
Let's this characterization it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by {
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    · apply min_le_right
    · apply min_le_left
  apply le_antisymm; repeat apply h
  }


lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {
  apply le_antisymm
  · apply le_min
    · apply le_min
      · apply min_le_left
      · apply le_trans
        apply min_le_right
        apply min_le_left
    · apply le_trans
      apply min_le_right
      apply min_le_right
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    · apply le_min
      · apply le_trans
        apply min_le_left
        apply min_le_right
      · apply min_le_right
  }



/- Prove that the following function is continuous.
You can use `Continuous.div` as the first step,
and use the search techniques to find other relevant lemmas.
`ne_of_lt`/`ne_of_gt` will be useful to prove the inequality. -/
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {
  apply Continuous.div
  · apply Continuous.mul
    · have h : Continuous (fun x : ℝ => x^5) := by apply continuous_pow 5;
      exact continuous_sin.comp h
    · exact continuous_cos
  · apply Continuous.add
    · apply continuous_pow 2
    · apply continuous_const
  have h1 : ∀ (x : ℝ), x ^ 2 ≥ 0 := by apply sq_nonneg
  intro x
  apply ne_of_gt
  calc
      x ^ 2 + 1 ≥ 0 + 1 := by apply add_le_add_right (h1 x)
      _ = 1 := by norm_num
      _ > 0 := by norm_num
  }

/- Prove this only using `intro`/`constructor`/`obtain`/`exact` -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intro p q
  constructor
  · intro (hpq : p ∧ q)
    obtain ⟨h₁, h₂⟩ := hpq
    exact ⟨h₂, h₁⟩
  · intro (hqp : q ∧ p)
    obtain ⟨h₃, h₄⟩ := hqp
    exact ⟨h₄, h₃⟩
}

/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  unfold Nondecreasing
  intro x₁ x₂
  intro h
  simp
  unfold Nondecreasing at hg hf
  have h₁ : f x₁ ≤ f x₂ := by apply hf x₁ x₂ h
  have h₂ : g x₁ ≤ g x₂ := by apply hg x₁ x₂ h
  apply hg
  apply hf
  exact h
  }


/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)`.
  `simp` can simplify `(f + g) x` to `f x + g x`. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
  unfold Nondecreasing
  intro x₁ x₂
  intro h
  simp
  unfold Nondecreasing at hf hg
  have h₁ : f x₁ ≤ f x₂ := by apply hf x₁ x₂ h
  have h₂ : g x₁ ≤ g x₂ := by apply hg x₁ x₂ h
  linarith
  }



/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  unfold EvenFunction
  unfold EvenFunction at hf
  constructor
  · simp
    intro h
    intro x
    specialize hf x
    specialize h x
    rw [hf] at h
    linarith

  · simp
    intro h
    intro x
    specialize hf x
    specialize h x
    linarith
  }
