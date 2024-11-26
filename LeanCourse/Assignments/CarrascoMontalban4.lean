import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  unfold univ
  constructor
  · intro hx
    rw [hx]
    simp
  · intro hx
    ext x
    simp_all only [setOf_true, mem_univ]
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  sorry
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  sorry
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  sorry
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  sorry
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
  unfold SequentialLimit at *
  simp
  intro ε hε
  specialize hs ε
  obtain ⟨N, hN⟩ := hs hε
  specialize hr N
  obtain ⟨N₁, hN₁⟩ := hr
  exact Exists.intro N₁ $ fun n a ↦ hN (r n) (hN₁ n a)
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  unfold SequentialLimit at *
  simp
  intro ε hε
  specialize hs₁ ε
  specialize hs₃ ε
  obtain ⟨N₁, hN₁⟩ := hs₁ hε
  obtain ⟨N₃, hN₃⟩ := hs₃ hε
  let N₀ := max N₁ N₃
  have h_N₀ : N₀ = max N₁ N₃ := rfl
  use N₀
  intro n
  specialize hN₁ n
  specialize hN₃ n
  intro hN₀
  specialize hs₁ hε
  specialize hs₃ hε
  have h1 : N₁ ≤ n := by exact le_of_max_le_left hN₀
  have h2 : N₃ ≤ n := by exact le_of_max_le_right hN₀
  refine abs_sub_lt_iff.mpr ?h.a
  have h₁ :
     s₂ n - a ≤ s₃ n - a := by linarith [hs₂s₃ n]
  have h₂ :
    s₃ n - a < ε := by exact (abs_lt.mp (hN₃ h2)).2
  have h₃ :
    s₂ n - a ≥ s₁ n - a := by linarith [hs₁s₂ n]
  have h₄ :
    s₁ n - a > -ε := by exact (abs_lt.mp (hN₁ h1)).1
  constructor
  · linarith
  · linarith

  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext x
  constructor
  · simp
    intro x₁ hx₁ hx₂ hx₃
    use x₁
    constructor
    · constructor
      · exact hx₁
      · rw [hx₂]; exact hx₃
    · exact hx₂
  · simp
    intro x₁ hx₁ hx₂ hx₃
    constructor
    · use x₁
    · rw [← hx₃]; exact hx₂
  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  constructor
  · simp
    intro h
    by_contra h1
    push_neg at h1
    obtain ⟨h2, h3⟩ := h1
    have h4 : x ^ 2 < 16 := by nlinarith [h2, h3]
    exact not_le_of_gt h4 h

  · simp
    intro h
    by_contra h1
    push_neg at h1
    cases h with
    | inl h2 =>
      have : x ^ 2 ≥ 16 := by nlinarith [h2]
      linarith
    | inr h3 =>
      have : x ^ 2 ≥ 16 := by nlinarith [h3]
      linarith
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/


-- READ NOTE LATER - WE JUSTIFY WHY WE INTRODUCE THESE DEFINITIONS


def conditionalInverse' (y : β)
  (h : ∃ x ∈ s, f x = y) : α :=
  Classical.choose h

lemma invFun_spec' (y : β) (h : ∃ x ∈ s, f x = y)  :
    (conditionalInverse' f s y h) ∈ s ∧ f (Classical.choose h) = y :=
  Classical.choose_spec h

/- We can now define the function by cases
on whether it lies in the range of `f` or not. -/

def inverse' [Inhabited α] (f : α → β) (y : β) : α :=
  if h : ∃ x ∈ s, f x = y then
    conditionalInverse' f s y h else default


-- NOTE (READ): WE HAVE SLIGHTLY CHANGED SOME CHOICE-RELATED DEFINITIONS IN ORDER TO MAKE
-- THEM MORE ADEQUATE FOR THE PROOFS. THEY'RE EQUIVALENT - THE UNIQUE DIFFERENCE BETWEEN THEM
-- IS THE RESTRICTION TO s. THOSE DEFINITIONS COULD ALSO HAVE BEEN DONE THROGHOUT THE PROOF
-- SO IN ORDER TO AVOID UNCLARITY WE'VE DECIDED TO DECLARE THEM APART

lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  let g : β → α := inverse' s f
  use g
  unfold LeftInvOn
  intro x hx
  unfold g
  have h' : ∃ x₁ ∈ s, f x₁ = f x := by use x
  simp [inverse', h']
  apply hf
  · exact (invFun_spec' f s (f x) h').1
  · exact hx
  · exact (invFun_spec' f s (f x) h').2
}

#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of simp to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by {
  by_contra h
  push_neg at h
  obtain ⟨x, y, hxy⟩ := h

  have hx : f x ∈ range f := by exact mem_range_self x
  have hxg : g y ∈ range g := by exact mem_range_self y
  have hxfg : f x ∈ range g := by rw[← hxy] at hxg; exact hxg
  have hxr : f x ∈ range f ∩ range g := by exact mem_inter hx hxfg
  rw[h1] at hxr
  contradiction
  }
  have h1'' : ∀ y x, g y ≠ f x := by exact fun y x a ↦ h1' x y (id (Eq.symm a))
  have h2' : ∀ x, x ∈ range f ∪ range g := by {
    intro x
    rw[h2]
    trivial
  }
  let L : Set α × Set β → Set γ := fun (x, y) ↦ (f '' x) ∪ (g '' y)
  let R : Set γ → Set α × Set β := fun x ↦ (f ⁻¹' (x), g ⁻¹' (x))

  use L, R
  constructor
  · ext X y
    unfold L R
    constructor
    · intro h
      simp at h
      simp only [id_eq]
      obtain hl|hr := h
      · obtain ⟨x₀, hx₀, hxy₀⟩ := hl
        rw[hxy₀] at hx₀
        exact hx₀
      · obtain ⟨x₀, hx₀, hxy₀⟩ := hr
        rw[hxy₀] at hx₀
        exact hx₀
    · intro h
      simp
      simp[id_eq] at h
      have h' : (∃ x, f x = y) ∨ (∃ x, g x = y) := by exact h2' y
      obtain h'l|h'r := h'
      · left
        obtain ⟨x, hx⟩ := h'l
        use x
        rw[← hx] at h
        trivial
      · right
        obtain ⟨x, hx⟩ := h'r
        use x
        rw[← hx] at h
        trivial
  · unfold R L
    ext x y
    · simp
      constructor
      intro h
      obtain hL|hR := h
      · obtain ⟨z, hz1, hz2⟩ := hL
        apply hf at hz2
        rw[hz2] at hz1
        exact hz1
      · obtain ⟨z, hz1, hz2⟩ := hR
        exfalso
        have hx : f y ∈ range f := by exact mem_range_self y
        have hxg : g z ∈ range g := by exact mem_range_self z
        have hxfg : f y ∈ range g := by rw[hz2] at hxg; exact hxg
        have hxr : f y ∈ range f ∩ range g := by exact mem_inter hx hxfg
        rw[h1] at hxr
        contradiction
      · intro h
        · left
          use y
    · simp
      constructor
      · intro h
        obtain hL|hR := h
        · obtain ⟨x₁, hx₁, h'x₁⟩ := hL
          exfalso
          have hx : f x₁ ∈ range f := by exact mem_range_self x₁
          have hxg : g y ∈ range g := by exact mem_range_self y
          have hxfg : f x₁ ∈ range g := by rw[← h'x₁] at hxg; exact hxg
          have hxr : f x₁ ∈ range f ∩ range g := by exact mem_inter hx hxfg
          rw[h1] at hxr
          contradiction
        · obtain ⟨x₁, hx₁, h'x₁⟩ := hR
          apply hg at h'x₁
          rw[← h'x₁]
          exact hx₁
      · intro h
        · right
          use y
  }
