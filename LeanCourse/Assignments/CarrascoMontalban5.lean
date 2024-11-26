import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
  -- simp [myThree] -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)
  sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  sorry
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  sorry
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  sorry
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  sorry
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  sorry
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  sorry
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  sorry
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  sorry
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  sorry
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  sorry
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  sorry
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  sorry
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  sorry
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  sorry
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  sorry
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here


/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here



/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry



/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here

@[ext] structure strict_bipointed (α : Type*) where
  x : α
  y : α
  distinct : x ≠ y

-- state and prove the lemma here

lemma str_bip_dis (α : Type*) (s : strict_bipointed α) :
      ∀ z : α, z ≠ s.x ∨ z ≠ s.y := by
      intro z
      by_cases h : z = s.x
      · right
        rw [h]
        exact s.distinct
      · left
        exact h


/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in


-- We'll use the following lemma from the lectures
lemma sq_aux (n : ℕ) : ∑ i in range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring
  }

lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
   induction n with
   | zero => norm_num
   | succ n ih =>
     rw [Finset.sum_range_succ, ih, sq_aux]
     simp only [sq_aux]
     field_simp
     ring
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  constructor
  · rw [@pairwise_disjoint_on]
    intro i j hij
    rw [@Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro h
      rw [hC, hC] at h
      simp at h
      obtain ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ := h
      simp_all only [not_lt]
    · intro h
      contradiction

  · ext x
    constructor
    · intro h
      simp at h
      obtain ⟨i, hi⟩ := h
      simp_all only [not_lt, mem_diff, mem_iUnion, exists_prop, not_exists, not_and]
      obtain ⟨h₁, h₂⟩ := hi
      exact Exists.intro i h₁

    · intro h
      simp at h
      obtain ⟨i, hi⟩ := h
      simp
      let s := {k | x ∈ A k}
      have hs : s.Nonempty := ⟨i, hi⟩
      obtain ⟨j, hj, hmin⟩ := h s hs
      use j
      rw [hC j]
      apply And.intro
      · exact hj
      · simp at hmin
        rw [@mem_iUnion₂]
        push_neg
        intro i hij
        by_contra h_i
        have : i ∈ s := h_i
        exact hij.not_le $ hmin i this
  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma aux_not_prime (n x y : ℕ) (h₁ : 2 ≤ x) (h₂ : 2 ≤ y) (h₃ : n = x * y) :
    ¬Nat.Prime (x * y) := by {
    refine not_prime_mul ?_ ?_
    · exact Ne.symm $ Nat.ne_of_lt h₁
    · exact Ne.symm $ Nat.ne_of_lt h₂
}

-- The last auxiliar lemma will help us to prove the following result

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  constructor
  · intro h
    cases n with
    | zero => simp
    | succ n =>
    cases n with
    | zero => simp
    | succ n => {
      simp at *
      rw [Nat.prime_def_lt] at h
      push_neg at h
      have h1 := h $ by linarith
      obtain ⟨m, h2, h3, h4⟩ := h1
      have hm : m ≠ 0 := by{
      simp
      by_contra hmm
      rw [hmm] at h3
      omega
      }
      have hm2 : 2 ≤ m := by {
          cases m with
          | zero => contradiction
          |  succ m =>
            cases m with
            | zero => contradiction
            | succ m => linarith
        }
      use m
      constructor
      · exact hm2
      · obtain ⟨m', hm'⟩ := h3
        use m'
        constructor
        · nlinarith
        · exact hm'
    }

  · intro h
    rcases h with ⟨x, rfl⟩|⟨x, rfl⟩|⟨x, y, h⟩
    · exact Nat.not_prime_zero
    · exact Nat.not_prime_one
    · obtain ⟨h₁, h₂, h₃⟩ := h
      rw [h₃]
      apply aux_not_prime
      · exact h₁
      · exact h₂
      · trivial

  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn; contradiction
  · simp at hn; contradiction
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by ring; trivial
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by {
        have h : (2 : ℤ) ^ a  ≡ 1 [ZMOD (2 : ℤ) ^ a - 1] := by exact Int.modEq_sub (2 ^ a) 1
        have h_pow := Int.ModEq.pow b h
        exact Int.ModEq.sub h_pow rfl
      }
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by ring; rfl
  have h2  : 2 ^ 2 ≤ 2 ^ a := by rw [propext (Nat.pow_le_pow_iff_right le.refl)]; exact ha
  have h3 : 1 ≤ 2 ^ a := by exact Nat.one_le_two_pow
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    have haa : 0 < a := by linarith
    have hbb : 0 < b := by linarith
    refine (Nat.pow_lt_pow_iff_right ?_).mpr ?_
    · nlinarith
    · nlinarith
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by simp; exact Nat.one_le_two_pow
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  simp at *
  have hgt_one : 1 < 2 ^ a - 1 := by {
    have hh : 2 < 2 ^ a := by nlinarith
    have hhh : 1 < 2 ^ a - 1 := by {
    have hhhh : 4 ≤ 2 ^ a := by nlinarith
    have h₁ : 3 ≤ 2 ^ a - 1 := by exact (Nat.le_sub_one_iff_lt h3).mpr h2
    linarith
    }
    exact hhh
  }
  have prime_cond := hn.2
  have h' : (2 ^ a - 1 : ℕ) ∣ 2 ^ (a * b) - 1 := by
    norm_cast at h
  specialize prime_cond ((2 : ℕ) ^ a - 1) h5 h'
  nlinarith
  }

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  unfold IsSquare
  by_cases h : a = b
  · left
    by_contra hr
    rw[← h] at hr
    obtain ⟨ r, hr'⟩ := hr
    ring at hr'
    have ha' : a^2 < a^2 + a := by linarith
    have := calc a^2 + a
      _= a*(a+1):= by ring
      _< (a+1)*(a+1) := by linarith
      _= (a+1)^2 := by ring
    have hr'' : a ^ 2 + a = r ^ 2 := by linarith
    rw[hr''] at ha'
    rw[hr''] at this
    have har : a < r := by exact lt_of_pow_lt_pow_left' 2 ha'
    have har1 : r < a + 1 := by exact lt_of_pow_lt_pow_left' 2 this
    linarith
  by_cases h2 : a < b
  · right
    by_contra hr
    obtain ⟨r, hr'⟩ := hr
    ring at hr'
    have hba : b^2 < a + b ^2 := by linarith
    have hab : a + b ^2 < (b+1)^2 := by linarith
    have hr'' : r ^ 2 = a + b ^ 2 := by linarith
    rw[← hr''] at hba hab
    have hbr : b < r := by exact lt_of_pow_lt_pow_left' 2 hba
    have hbr1 : r < b + 1 := by exact lt_of_pow_lt_pow_left' 2 hab
    linarith
  simp at h2
  have h3 : b < a := by exact Nat.lt_of_le_of_ne h2 fun a_1 ↦ h $ id (Eq.symm a_1)
  · left -- note that we just have to repeat the previous proof changing a and b
    by_contra hr
    obtain ⟨r, hr'⟩ := hr
    ring at hr'
    have hba : a^2 < b + a ^2 := by linarith
    have hab : b + a ^2 < (a+1)^2 := by linarith
    have hr'' : r ^ 2 = b + a ^ 2 := by linarith
    rw[← hr''] at hba hab
    have hbr : a < r := by exact lt_of_pow_lt_pow_left' 2 hba
    have hbr1 : r < a + 1 := by exact lt_of_pow_lt_pow_left' 2 hab
    linarith
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

-- SOME PROPERTIES CAN BE DIRECTLY INHERITED FROM ℝ, BUT OTHERS NEED TO BE REFINED

def groupPosReal : Group PosReal where
 mul x y := x * y
 one := 1 -- inherited from ℝ since 1 ∈ ℝ
 inv x := ⟨x.val⁻¹, inv_pos.mpr x.property⟩
 mul_assoc x y z := mul_assoc x y z
 one_mul x := one_mul x
 mul_one x := mul_one x
 inv_mul_cancel x := by refine Eq.symm (Subtype.eq ?_); field_simp; rw [div_self (ne_of_gt x.property)]

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
     induction s using Finset.induction with
     | empty => simp
     | @insert x s hxs ih =>
       rw [Finset.powerset_insert, Finset.card_insert_of_not_mem]
       rw [@card_union]
       -- But x ∉ s, so (s.powerset ∩ Finset.image (insert x) s.powerset).card has to be 0
       have empty_interc : s.powerset ∩ Finset.image (insert x) s.powerset = ∅ := by {
        ext A
        constructor
        · intro h
          simp at h
          by_contra h1
          have h₁ : x ∈ insert x A := by exact mem_insert_self x A
          obtain ⟨ha, haa⟩ := h
          obtain ⟨a, h2, h3⟩ := haa
          have h4 : x ∈ insert x a := by exact mem_insert_self x a
          rw [h3] at h4
          have h5 : x ∈ s := ha h4
          contradiction
        · intro h
          contradiction}
       have h : (s.powerset ∩ Finset.image (insert x) s.powerset).card = 0 := by exact Finset.card_eq_zero.mpr empty_interc
       rw [h, ih]
       simp
       have h' : (Finset.image (insert x) s.powerset).card = s.powerset.card := by {
        refine card_image_iff.mpr ?_
        unfold InjOn
        intro x1 h1 x2 h2 hxx1x2
        have h6 : ∀ Y, Y ∈ s.powerset → x ∉ Y := by exact fun Y a ↦ not_mem_of_mem_powerset_of_not_mem a hxs
        have h7 := h6 x1 h1
        have h8 := h6 x2 h2
        ext y
        constructor
        intro hx1
        have hy : y ≠ x := by exact ne_of_mem_of_not_mem hx1 (h6 x1 h1)
        have hyx1 : y ∈ insert x x1 := by exact Finset.mem_insert_of_mem hx1
        rw[hxx1x2] at hyx1
        exact Finset.mem_of_mem_insert_of_ne hyx1 hy
        intro hx2
        have hy : y ≠ x := by exact ne_of_mem_of_not_mem hx2 (h6 x2 h2)
        have hyx2 : y ∈ insert x x2 := by exact Finset.mem_insert_of_mem hx2
        rw[← hxx1x2] at hyx2
        exact Finset.mem_of_mem_insert_of_ne hyx2 hy
       }
       rw[h', ih]; ring
       assumption
    }
