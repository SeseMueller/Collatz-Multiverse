import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Use

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Logic.Function.Iterate

import Aesop

import Batteries.Tactic.GeneralizeProofs



-- Inspired by CaryKH's Collatz Multiverse video: https://www.youtube.com/watch?v=n63FBYqj98E
-- In this repositiory, I want to formalize and prove some of the claims made in that video.

-- We define a Collatz Universe to be an object that contains two Natural Numbers as parameters.
-- It is used as a data structure to decide what to do in the Collatz function, specifically
-- in the odd case.
-- The multiplier (standard: 3) will be what the number is multiplied by in the odd case,
-- and the adder (standard: 1) will be what is added to the number in the odd case.
structure CollatzUniverse where
  multiplier : ℕ
  adder : ℕ
deriving Repr

-- We need to tell lean that there is a way to tell whether a natural number is even or not.
@[reducible]
def NatEvenDecidable := Nat.instDecidablePredEven

def applyCollatz (u : CollatzUniverse) (n : ℕ) : ℕ :=
  if Even n then
    n / 2
  else
    u.multiplier * n + u.adder

-- We are interested in the repeated application of this function,
-- so we define a function that applies the Collatz function k times to a number n.
def applyCollatzKTimes (u : CollatzUniverse) (n : ℕ) (k : ℕ) : ℕ :=
  if k = 0 then
    n
  else
    applyCollatzKTimes u (applyCollatz u n) (k - 1)

-- We call a Collatz Universe a "Hub-and-Spoke" universe if the multiplier is 0.
-- These Universes are characterized by the fact that all odd numbers are sent to the same number
-- (the adder, and, visually, the "hub").
def isHubAndSpoke (u : CollatzUniverse) : Prop :=
  u.multiplier = 0

-- Theorem: In a Hub-and-Spoke universe, all odd numbers are sent to the adder of the universe.
theorem oddNumbersSentToSameNumberInHubAndSpoke (u : CollatzUniverse) (n : ℕ) (h : isHubAndSpoke u)
(hn : Odd n) : applyCollatz u n = u.adder := by
  unfold applyCollatz
  unfold isHubAndSpoke at h
  simp [h, hn]

-- In a Hub-and-Spoke universe, all numbers eventually end up
-- at the adder. This is because even numbers keep getting divided by 2 until they become odd,
-- and then they get sent to the adder. (Exception: 0.)
theorem allNumbersEndUpAtAdderInHubAndSpoke (u : CollatzUniverse) (n : ℕ) (h : isHubAndSpoke u) :
∃ k : ℕ, 0 < k → n = 0 ∨ applyCollatzKTimes u n k = u.adder := by
  -- Proof goes here
  -- the behaviour depends on the starting number.
  -- I think I can do some generalized induction on the number...
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- First, do the 0 case, because else it makes the whole proof more cumbersome.
    by_cases h_zero : n = 0
    · use 0
      simp [h_zero]
    -- Remove the 0 case from the rest of the goal.
    convert_to ∃ k, 0 < k → applyCollatzKTimes u n k = u.adder
    · simp_all only [false_or]
    -- Depending on whether n is even or odd, we have two cases.
    by_cases h_odd : Odd n
    · use 1
      unfold applyCollatzKTimes
      simp only [zero_lt_one, one_ne_zero, ↓reduceIte, tsub_self, forall_const]
      unfold applyCollatzKTimes
      simp only [↓reduceIte]
      exact oddNumbersSentToSameNumberInHubAndSpoke u n h h_odd
    · have h_even : Even n := Nat.not_odd_iff_even.mp h_odd
      have h_half : n / 2 < n := Nat.bitwise_rec_lemma h_zero
      obtain ⟨k, hk⟩ : ∃ k, 0 < k → n / 2 = 0 ∨ applyCollatzKTimes u (n / 2) k = u.adder :=
        ih (n / 2) h_half
      sorry


-- TODO: maybe prove the bi-angle or tri-angle nature of hub-and-spoke universes
-- with an adder which is a power of 2?

-- TODO: Prove the statement about period doubling in the Hub-and-Spoke universes


-- We call a universe with an adder of 0 a "Shape Universe", since all multipliers which are
-- a power of 2 give rise to shapes with log_2(n) sides (or more precisely, edges).
def isShapeUniverse (u : CollatzUniverse) : Prop :=
  u.adder = 0

-- In the Shape universe with multiplier 1, odd numbers are sent to themselves.
theorem oddNumbersSentToThemselvesInShapeUniverseWithMultiplierOne (u : CollatzUniverse) (n : ℕ)
(h : isShapeUniverse u) (h_mult : u.multiplier = 1) (h_odd : Odd n) : applyCollatz u n = n := by
  unfold applyCollatz
  simp_all only [← Nat.not_even_iff_odd, ↓reduceIte, one_mul, Nat.add_eq_left]
  exact h

-- We call a universe "bounded", if for all nubers, there exists a k and N such that
-- applying the Collatz function k times to the number results in a number
-- less than or equal to N.
def isBounded (u : CollatzUniverse) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ k : ℕ, applyCollatzKTimes u n k ≤ N
-- This means that all numbers eventually end up in a cycle, and that there are no
-- divergent trajectories. However, it does not limit the size or number of the cycles.
-- Also note that this does not mean that the cycle needs to include, or even include
-- or contain lower numbers than the starting number.

/- Start of Aristotle.

--
Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4f5752ee-8169-4046-a039-b78a5ec0e308

The following was proved by Aristotle:

- theorem shapeUniversesWithPowerOfTwoMultipliersAreBounded (u : CollatzUniverse)
(h : isShapeUniverse u) (m : ∃ k : ℕ, u.multiplier = 2 ^ k) : isBounded u
--

It generated a lot of auxillery lemmas as the task I gave it was quite complex.
I have cleaned up these lemmas and switched them to the actual Even/Odd predicates
instead of n % 2 = 0 or n % 2 = 1, but the core of the proof is still the same as Aristotle's.

-/

-- We can show that the Shape Universes with a multiplier which is a power of 2 are bounded.
noncomputable section AristotleLemmas

lemma applyCollatzKTimes_zero (u : CollatzUniverse) (n : ℕ) : applyCollatzKTimes u n 0 = n := by
  unfold applyCollatzKTimes; simp

/-
If we start with `2^k * n`, applying Collatz `k` times results in `n`.
This is because `2^k * n` is even, so we divide by 2 repeatedly.
-/
lemma applyCollatzKTimes_power_of_two_mul (u : CollatzUniverse) (n k : ℕ) :
applyCollatzKTimes u (2^k * n) k = n := by
  have h_div : ∀ m : ℕ, applyCollatzKTimes u (2 ^ m * n) m = n := by
    -- intro m; induction m <;> simp_all +decide [Nat.pow_zero, Nat.one_mul] ;
    intro m; induction m;
    · unfold applyCollatzKTimes; simp_all only [↓reduceIte, Nat.pow_zero, Nat.one_mul];
    · -- By definition of applyCollatzKTimes, we can rewrite the left-hand side.
      expose_names;
      have h_apply : applyCollatzKTimes u (2 * (2 ^ ‹_› * n)) (‹_› + 1) =
      applyCollatzKTimes u (applyCollatz u (2 * (2 ^ ‹_› * n))) ‹_› := by
        rw [applyCollatzKTimes];
        rfl
      -- Aristotle didn't give me the 100% correct proof here for some reason,
      --- my environment is probably weird.
      have: (2 ^ (n_1 + 1) * n) = (2 * (2 ^ n_1 * n)) := by
        rw [Nat.pow_succ']
        exact Nat.mul_assoc 2 (2 ^ n_1) n
      convert_to applyCollatzKTimes u (2 * (2 ^ n_1 * n)) (n_1 + 1) = n
      · exact
        Nat.succ_inj.mp
          (congrArg Nat.succ (congrFun (congrArg (applyCollatzKTimes u) this) (n_1 + 1)))
      rw [h_apply];
      unfold applyCollatz; aesop;
  exact h_div k

/-
In a Shape Universe with multiplier `2^m`, applying the Collatz function to an odd number `n`
results in `2^m * n`.
-/
lemma shape_odd_step (u : CollatzUniverse) (m : ℕ) (h_shape : isShapeUniverse u)
  (h_mult : u.multiplier = 2 ^ m) (n : ℕ) (h_odd : Odd n) : applyCollatz u n = 2^m * n := by
  unfold applyCollatz;
  simp_all only [← Nat.not_even_iff_odd, ↓reduceIte, Nat.add_eq_left]
  exact h_shape;

/-
In a Shape Universe with multiplier `2^m`, applying the Collatz function `m+1` times
to an odd number `n` returns `n`. This is because the first step multiplies by `2^m`
(since adder is 0), and the next `m` steps divide by 2.
-/
lemma shape_odd_return (u : CollatzUniverse) (m : ℕ) (h_shape : isShapeUniverse u)
(h_mult : u.multiplier = 2 ^ m) (n : ℕ) (h_odd : Odd n) :
applyCollatzKTimes u n (m + 1) = n := by
  convert applyCollatzKTimes_power_of_two_mul u n m using 1;
  rw [ show applyCollatzKTimes u n ( m + 1 ) = applyCollatzKTimes u ( applyCollatz u n ) m
    from ?_, shape_odd_step u m h_shape h_mult n h_odd ];
  -- By definition of applyCollatzKTimes, we can rewrite the left-hand side as the right-hand side.
  rw [applyCollatzKTimes];
  rfl

/-
Applying Collatz `a + b` times is the same as applying it `a` times,
and then applying it `b` times to the result.
-/
lemma applyCollatzKTimes_add (u : CollatzUniverse) (n a b : ℕ) : applyCollatzKTimes u n (a + b) =
applyCollatzKTimes u (applyCollatzKTimes u n a) b := by
  -- By definition of `applyCollatzKTimes`, we can rewrite the right-hand side of the equation
  -- using the recursive definition.
  have h_apply : ∀ n k, applyCollatzKTimes u n k = Nat.iterate (applyCollatz u) k n := by
    intro n k; induction k <;>
      simp_all +decide only [Function.iterate_zero, id_eq, Function.iterate_succ_apply'] ;
    · unfold applyCollatzKTimes; simp_all only [↓reduceIte];
    · -- By definition of `applyCollatzKTimes`, we have
      -- `applyCollatzKTimes u n (k + 1) = applyCollatzKTimes u (applyCollatz u n) k`.
      have h_def : ∀ n k, applyCollatzKTimes u n (k + 1) =
      applyCollatzKTimes u (applyCollatz u n) k := by
        intros n k
        rw [applyCollatzKTimes];
        rfl;
      -- By induction on $k$, we can show that applyCollatzKTimes u n k is equal to the iterate
      -- of applyCollatz u applied $k$ times to $n$.
      have h_ind : ∀ k n, applyCollatzKTimes u n k = Nat.iterate (applyCollatz u) k n := by
        intro k; induction k <;>
          simp_all +decide only [Function.iterate_zero, id_eq, Function.iterate_succ_apply'] ;
        · unfold applyCollatzKTimes; aesop;
        · (expose_names; exact fun n ↦ Function.iterate_succ_apply' (applyCollatz u) n_3 n);
      rw [ h_ind, Function.iterate_succ_apply' ];
  rw [ h_apply, h_apply, h_apply, Function.iterate_add_apply ];
  rw [ ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply ]

/-
In a Shape Universe, if we start at `2^m * n`, the next `m` steps will just divide by 2 repeatedly,
yielding `2^(m-k) * n` at step `k`.
-/
-- This doesn't require a shape universe.
lemma shape_cycle_descent (u : CollatzUniverse) (m : ℕ) --(h_shape : isShapeUniverse u)
(h_mult : u.multiplier = 2 ^ m) (n : ℕ) :
  ∀ k ≤ m, applyCollatzKTimes u (2^m * n) k = 2^(m-k) * n := by
    intro k hk_le_m
    have h_ind : ∀ k ≤ m, applyCollatzKTimes u (2^m * n) k =
    applyCollatzKTimes u (2^(m-k) * n) 0 := by
      intros k hk_le_m
      have h_ind_step : ∀ k ≤ m, applyCollatzKTimes u (2^m * n) (k + 1) =
      applyCollatzKTimes u (2^(m-k) * n) 1 := by
        intros k hk_le_m
        have h_ind_step : applyCollatzKTimes u (2^m * n) (k + 1) =
        applyCollatzKTimes u (applyCollatzKTimes u (2^m * n) k) 1 := by
          exact applyCollatzKTimes_add u (2 ^ m * n) k 1;
        convert h_ind_step using 2;
        rw [ show 2 ^ m * n = 2 ^ k * ( 2 ^ ( m - k ) * n ) by
          rw [ ← Nat.mul_assoc, ← Nat.pow_add, add_tsub_cancel_of_le hk_le_m ],
            applyCollatzKTimes_power_of_two_mul ];
      cases k <;> simp_all +decide only [applyCollatzKTimes_add, zero_le, tsub_zero];
      rw [ h_ind_step _ ( by linarith ), Nat.sub_succ ];
      unfold applyCollatzKTimes; simp +decide only [↓reduceIte, Nat.mul_comm, tsub_self,
        Nat.pred_eq_sub_one] ;
      have even_power: ∀ a : ℕ, a ≥ 1 → Even (2 ^ a) :=
        by grind;
      have even_mul: ∀ a b : ℕ, Even b → Even (a * b) := fun a b a_1 ↦ Even.mul_left a_1 a;
      have even_power_mul : ∀ a b : ℕ, b ≥ 1 → Even (a * 2 ^ b) := by
        intros a b ha
        apply even_mul
        exact even_power b ha;
      unfold applyCollatz; simp +decide only [h_mult] ;
      cases h : m - ‹_› <;> simp_all +decide only [ne_eq, Nat.pow_succ', dvd_mul_right,
        Nat.mul_div_assoc, mul_div_cancel_left₀, add_tsub_cancel_right];
      · omega;
      · unfold applyCollatzKTimes; simp +decide only [↓reduceIte] ; norm_num
    rw [ h_ind k hk_le_m, applyCollatzKTimes ] ; aesop;

/-
If the trajectory of `n` returns to `n` after `p` steps, then the trajectory is periodic
with period `p`. Specifically, the value at step `k` is the same as the value at step `k % p`.
-/
lemma applyCollatzKTimes_periodic (u : CollatzUniverse) (n p : ℕ) (h : applyCollatzKTimes u n p = n)
: ∀ k, applyCollatzKTimes u n k = applyCollatzKTimes u n (k % p) := by
  intro k
  rw [← Nat.mod_add_div k p];
  induction k / p <;> simp_all +decide [ Nat.mul_succ, ← add_assoc ];
  -- By definition of applyCollatzKTimes, we have applyCollatzKTimes u n (k % p + p) =
  -- applyCollatzKTimes u (applyCollatzKTimes u n (k % p)) p.
  have h_apply : ∀ a b : ℕ, applyCollatzKTimes u n (a + b) =
  applyCollatzKTimes u (applyCollatzKTimes u n a) b := by
    exact fun a b ↦ applyCollatzKTimes_add u n a b;
  grind +ring

/-
In a Shape Universe with multiplier `2^m`,
the trajectory of an odd number `n` is bounded by `2^m * n`.
-/
lemma shape_cycle_max (u : CollatzUniverse) (m : ℕ) (h_shape : isShapeUniverse u)
(h_mult : u.multiplier = 2 ^ m) (n : ℕ) (h_odd : Odd n) :
∀ k, applyCollatzKTimes u n k ≤ 2^m * n := by
  intro k
  set r := k % (m + 1) with hr
  have h_r_le : applyCollatzKTimes u n r ≤ 2 ^ m * n := by
    by_cases hr0 : r = 0;
    · rw [ hr0 ];
      unfold applyCollatzKTimes; norm_num; nlinarith [ Nat.one_le_pow m 2 zero_lt_two ] ;
    · -- Since `r > 0`, let `r = s + 1`.
      -- Then `applyCollatzKTimes u n r = applyCollatzKTimes u (applyCollatz u n) s`.
      obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := Nat.exists_eq_succ_of_ne_zero hr0
      have h_r_step : applyCollatzKTimes u n r = applyCollatzKTimes u (applyCollatz u n) s := by
        rw [ hs, applyCollatzKTimes ] ; aesop;
      have h_applyCollatz : applyCollatz u n = 2 ^ m * n := by
        exact shape_odd_step u m h_shape h_mult n h_odd
      rw [h_applyCollatz] at h_r_step
      have h_cycle : applyCollatzKTimes u (2 ^ m * n) s ≤ 2 ^ m * n := by
        have h_cycle : applyCollatzKTimes u (2 ^ m * n) s = 2 ^ (m - s) * n := by
          apply shape_cycle_descent u m h_mult n s (by
          linarith [ Nat.mod_lt k ( Nat.succ_pos m ) ])
        generalize_proofs at *; (
        exact h_cycle.symm ▸ Nat.mul_le_mul_right _
          ( pow_le_pow_right₀ ( by decide ) ( Nat.sub_le _ _ ) ))
      rw [h_r_step]
      exact h_cycle
  exact (by
  rw [ applyCollatzKTimes_periodic u n ( m + 1 )
    ( shape_odd_return u m h_shape h_mult n h_odd ) ] ; exact h_r_le;)

/-
Applying Collatz `k` times to `2^a * b` (where `k <= a`) results in `2^(a-k) * b`.
This is because the number remains even and we keep dividing by 2.
-/
lemma applyCollatzKTimes_pow_two_descent (u : CollatzUniverse) (a b k : ℕ) (hk : k ≤ a) :
applyCollatzKTimes u (2^a * b) k = 2^(a-k) * b := by
  revert k b a hk;
  have h_ind : ∀ a b : ℕ, applyCollatzKTimes u (2^a * b) a = b := by
    exact fun a b ↦ applyCollatzKTimes_power_of_two_mul u b a;
  intro a b k hk_le_a
  have h_ind_step : applyCollatzKTimes u (2^a * b) k =
  applyCollatzKTimes u (2^(a-k) * (2^k * b)) k := by
    rw [ ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk_le_a ];
  convert h_ind _ _ using 1 ;
  · ring_nf;
    convert h_ind_step using 2 ;
    · ring_nf;
    ring

/-
For any number `n`, applying the Collatz function repeatedly will eventually result in an odd number
or 0. This is because if the number is even, we divide by 2, strictly decreasing it (unless it's 0).
-/
lemma eventually_odd_or_zero (u : CollatzUniverse) (n : ℕ) : ∃ k, Odd (applyCollatzKTimes u n k) ∨
applyCollatzKTimes u n k = 0 := by
  by_contra h_no_odd_or_zero;
  -- Let's apply the definition of `applyCollatzKTimes` repeatedly.
  have h_def : ∀ k, applyCollatzKTimes u n (k + 1) = applyCollatz u (applyCollatzKTimes u n k) := by
    intro k
    rw [applyCollatzKTimes_add];
    rw [applyCollatzKTimes]
    simp only [one_ne_zero, ↓reduceIte, tsub_self];
    rw [ applyCollatzKTimes ] ;
    simp_all only [not_exists, not_or, ↓reduceIte];
  -- By definition of `applyCollatz`, if `applyCollatzKTimes u n k` is even,
  -- then `applyCollatzKTimes u n (k + 1) = applyCollatzKTimes u n k / 2`.
  have h_even_step : ∀ k, Even (applyCollatzKTimes u n k) → applyCollatzKTimes u n (k + 1) =
  applyCollatzKTimes u n k / 2 := by
    unfold applyCollatz at *;
    intro k a
    simp_all only [not_exists, not_or, ↓reduceIte];
  -- Since `applyCollatzKTimes u n k` is always even and positive, it must strictly decrease.
  have h_strict_decr : StrictAnti (fun k => applyCollatzKTimes u n k) := by
    exact strictAnti_nat_of_succ_lt (by grind only [= Nat.not_odd_iff_even, = Nat.odd_iff]);
  exact absurd ( Set.infinite_range_of_injective h_strict_decr.injective )
    ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr
      ⟨ _, Set.forall_mem_range.mpr fun k => h_strict_decr.antitone k.zero_le ⟩ )

end AristotleLemmas

-- We can show that the Shape Universes with a multiplier which is a power of 2 are bounded.

theorem shapeUniversesWithPowerOfTwoMultipliersAreBounded (u : CollatzUniverse)
(h : isShapeUniverse u) (m : ∃ k : ℕ, u.multiplier = 2 ^ k) : isBounded u := by
  unfold isShapeUniverse at h
  unfold isBounded
  intro n
  obtain ⟨k, m⟩ := m
  -- unfold applyCollatzKTimes
  -- Use `eventually_odd_or_zero` to find `k` such that `n_k = applyCollatzKTimes u n k`
  -- is either odd or 0.
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, Odd (applyCollatzKTimes u n k₀) ∨ applyCollatzKTimes u n k₀ = 0 :=
    eventually_odd_or_zero u n;
  -- Consider the set of values in the trajectory up to step
  -- `k₀`: `S = {applyCollatzKTimes u n i | i ≤ k₀}`.
  -- This set is finite, so it has a maximum `M_pre`.
  have h_finite : ∃ M_pre, ∀ i ≤ k₀, applyCollatzKTimes u n i ≤ M_pre := by
    exact ⟨ Finset.sup ( Finset.range ( k₀ + 1 ) ) fun i => applyCollatzKTimes u n i, fun i hi =>
      Finset.le_sup
        ( f := fun i => applyCollatzKTimes u n i ) ( Finset.mem_range_succ_iff.mpr hi ) ⟩;
  -- If `n_k = 0`, then the trajectory stays at 0 for all `j >= k₀`.
  by_cases h_zero : applyCollatzKTimes u n k₀ = 0;
  · -- Since `applyCollatz u 0 = 0`, the trajectory stays at 0 for all `j >= k₀`.
    have h_zero_trajectory : ∀ j ≥ k₀, applyCollatzKTimes u n j = 0 := by
      intro j hj; induction hj <;> simp_all +decide only [or_true, Nat.le_eq, Nat.succ_eq_add_one,
        applyCollatzKTimes_add] ;
      unfold applyCollatzKTimes; simp +decide only [↓reduceIte, applyCollatz, Nat.zero_div,
        tsub_self] ;
      unfold applyCollatzKTimes; simp +decide only [↓reduceIte] ;
    exact ⟨ Max.max h_finite.choose 0, fun j => if hj : j ≤ k₀ then
        le_trans ( h_finite.choose_spec j hj ) ( le_max_left _ _ )
      else
        le_trans ( le_of_eq ( h_zero_trajectory j ( le_of_not_ge hj ) ) ) ( le_max_right _ _ ) ⟩;
  · -- If `n_k` is odd, then let `n' = n_k`. By `shape_cycle_max`,
    -- for all `j`, `applyCollatzKTimes u n' j ≤ 2^k * n'`.
    obtain ⟨n', hn'⟩ : ∃ n', applyCollatzKTimes u n k₀ = n' ∧ Odd n' := by
      simp_all only [or_false, ↓existsAndEq, and_self]
    have h_shape_cycle : ∀ j, applyCollatzKTimes u n' j ≤ 2^k * n' := by
      apply shape_cycle_max u k h m n' hn'.right;
    -- Any step `t > k₀` can be written as `k₀ + j`.
    have h_step : ∀ t > k₀, applyCollatzKTimes u n t = applyCollatzKTimes u n' (t - k₀) := by
      intros t ht; rw [ ← hn'.1 ] ; rw [ ← Nat.add_sub_of_le ht.le ] ;
      simp +decide only [applyCollatzKTimes_add, add_tsub_cancel_left, hn'] ;
    exact ⟨ Max.max ( h_finite.choose ) ( 2 ^ k * n' ), fun t => if ht : t ≤ k₀ then
        le_trans ( h_finite.choose_spec t ht ) ( le_max_left _ _ )
      else
        le_trans ( h_step t ( not_le.mp ht ) ▸ h_shape_cycle _ ) ( le_max_right _ _ ) ⟩




-- The opposite of a bounded universe is an "unbounded" universe, where there exists a number
-- such that for all k, applying the Collatz function k times to the number results in a number
-- greater than the original number.
def isUnbounded (u : CollatzUniverse) : Prop :=
  ∃ n : ℕ, ∀ N : ℕ, ∃ k, applyCollatzKTimes u n k > N

theorem boundedEqNotUnbounded (u : CollatzUniverse) : isBounded u ↔ ¬ isUnbounded u := by
  simp [isBounded, isUnbounded]

-- Alternate way to write the definition of unboundedness:
-- There exists a number such that the function that maps k to
-- applying the Collatz function k times to the number is not bounded above.
def isUnbounded' (u : CollatzUniverse) : Prop :=
  ∃ n : ℕ, (Set.range (fun k => applyCollatzKTimes u n k)).Infinite


theorem unboundedIffUnbounded' (u : CollatzUniverse) : isUnbounded u ↔ isUnbounded' u := by
  unfold isUnbounded isUnbounded'
  constructor
  · rintro ⟨n, h⟩
    use n
    by_contra h_finite
    push_neg at h_finite
    let f := fun k => applyCollatzKTimes u n k
    let f_range := Set.range f
    -- This set has at least one element, since it contains applyCollatzKTimes u n 0 = n.
    have h_nonempty : f_range.Nonempty := by
      exact Set.range_nonempty f
    -- If the range is finite, then it has a maximum element M.
    obtain ⟨M, hM⟩ := Set.Finite.exists_maximal h_finite h_nonempty
    -- Now we can throw that M into h to get some k such that applyCollatzKTimes u n k > M,
    -- which is a contradiction.
    specialize h M
    obtain ⟨k, hk⟩ := h
    -- applyCollatzKTimes u n k is in the range of the function,
    -- so it must be less than or equal to M.
    have h_in_range : applyCollatzKTimes u n k ∈ f_range := by
      simp only [Set.mem_range, f_range]
      use k
    have h_le_M : applyCollatzKTimes u n k ≤ M := by
      exact Maximal.le hM h_in_range
    absurd hk
    push_neg
    exact h_le_M
  · rintro ⟨n, h⟩
    use n
    intro N
    by_contra h_not_gt
    push_neg at h_not_gt
    -- From h_not_gt, it would follow that the range of the function is bounded above by N,
    -- which contradicts h.
    have h_finite: Set.Finite (Set.range (fun k => applyCollatzKTimes u n k)) := by
      apply Set.finite_iff_bddAbove.mpr
      use N
      unfold upperBounds
      intro x hx
      grind only [= Set.mem_range]
    trivial

-- There exist universes which are runaway, in the sense that there exists a number
-- such that applying the Collatz repeatedly to the number results in pure growth.
-- This can easily be written as: the function that maps k to applying the Collatz function k times
-- to the number is monotonically increasing.
def isRunaway (u : CollatzUniverse) : Prop :=
  ∃ n : ℕ, StrictMono (fun k => applyCollatzKTimes u n k)

theorem runawayIffUnbounded (u : CollatzUniverse) :
  isRunaway u → isUnbounded u := by
  rintro ⟨n, h⟩
  use n
  intro N
  by_contra h_not_gt
  push_neg at h_not_gt
  -- Since the function is strictly monotone, it is injective, so its range is infinite.
  have h_infinite : Set.Infinite (Set.range (fun k => applyCollatzKTimes u n k)) := by
    exact Set.infinite_range_of_injective h.injective
  -- But if the function is not greater than N for any k, then its range is bounded above by N,
  -- which contradicts the fact that the range is infinite.
  have h_finite : Set.Finite (Set.range (fun k => applyCollatzKTimes u n k)) := by
    apply Set.finite_iff_bddAbove.mpr
    use N
    unfold upperBounds
    intro x hx
    grind only [= Set.mem_range]
  trivial

-- Another way to write the definition of runaway universes is that there exists a number
-- such that applying the Collatz function k+1 times to the number
-- is greater than applying it k times, for all k.
def isRunaway' (u : CollatzUniverse) : Prop :=
  ∃ n : ℕ, ∀ k : ℕ, applyCollatzKTimes u n (k + 1) > applyCollatzKTimes u n k

theorem runawayIffRunaway' (u : CollatzUniverse) :
  isRunaway u ↔ isRunaway' u := by
  constructor
  · rintro ⟨n, h⟩
    use n
    intro k
    tauto
  · rintro ⟨n, h⟩
    use n
    exact strictMono_nat_of_lt_succ h

-- If we are in a Shape Universe with an odd number multiplier > 2, then applying the Collatz
-- function k times to an odd number multiplies it by multiplier ^ k.
theorem shapeUniversesWithOddLargeTwoGrowExponentially (u : CollatzUniverse)
(h : isShapeUniverse u) (hodd : Odd u.multiplier) (i k : ℕ)
(hiodd : Odd i) :  applyCollatzKTimes u i k = i * (u.multiplier ^ k) := by
  revert i
  induction k with
  | zero =>
    simp [applyCollatzKTimes]
  | succ n Hn =>
    unfold applyCollatzKTimes
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_one_sub_one]
    intro i hiodd
    unfold isShapeUniverse at h
    have hinegeven := Nat.not_even_iff_odd.mpr hiodd
    have HApplOdd : Odd (applyCollatz u i) := by
      simp only [applyCollatz, hinegeven, ↓reduceIte, h, add_zero]
      exact Odd.mul hodd hiodd
    have HnAppl := Hn (applyCollatz u i) HApplOdd
    rw [HnAppl]
    simp [applyCollatz, hinegeven, h]
    ring1


-- We can show that the Shape Universes with odd numbers > 2 are all unbounded, as 1 explodes.
theorem shapeUniversesWithOddLargerTwoAreUnbounded (u : CollatzUniverse) (h : isShapeUniverse u)
(hodd : Odd u.multiplier) (hgt2 : u.multiplier > 2) : isUnbounded u := by
  have : ¬ isBounded u ↔ isUnbounded u := by simp [boundedEqNotUnbounded]
  rw [← this]
  simp only [isBounded, not_forall, not_exists, not_le]
  use 1
  intro low
  use low
  have temp := fun X => shapeUniversesWithOddLargeTwoGrowExponentially u h hodd 1 X (by decide)
  rw [temp]
  simp only [one_mul, gt_iff_lt]
  have : ∀ k : ℕ, k < 3 ^k := by
    intro k
    induction k with
    | zero => simp
    | succ n Hn =>
      grind
  have : ∀ k e : ℕ, e > 2 → k < e ^k := by
    clear * -
    intros k e he
    induction k with
    | zero => simp
    | succ n Hn =>
      ring_nf
      have : 1 < (e-1) * (e ^ n) := by
        have h1: 1 < e - 1 := by exact Nat.lt_sub_of_add_lt he
        have h2: 0 < e ^ n := by exact Nat.zero_lt_of_lt Hn
        exact one_lt_mul_of_lt_of_le' h1 h2
      have test := Nat.add_lt_add Hn this
      ring_nf at test
      convert_to n + 1 < e ^ n + (e ^ n) * (e - 1) using 1
      · ring
      · have temp : ∀ a b: ℕ, a > 1 → a * b = b + b * (a - 1) := by
          intros a b ha
          calc
            a * b = b * a := Nat.mul_comm a b
            b * a = b * (1 - 1 + a) := by ring
            _ = b * (a - 1 + 1) := by grind
            _ = b * (a - 1) + b := by ring
            _ = b + b * (a - 1) := by ring
        have test := temp e (e ^ n) (by exact Nat.lt_of_add_left_lt he)
        · exact test
      · exact Nat.one_add_le_iff.mp test
  exact Nat.lt_of_succ_le (this low u.multiplier hgt2)

-- In shape universes with a multiplier which is a power of 2 (that is, 2 ^ m),
-- all numbers eventually end up in a cycle,
-- where the cycle length is m + 1
-- For simplicity, we will only focus on prime numbers larger than 2.
-- Those immeadeately fall into the cycle without doing anything else.
theorem shapeUniversesWithPowerOfTwoMultipliersAreBounded' (u : CollatzUniverse)
(h : isShapeUniverse u) (n k : ℕ) (h_nprime : Nat.Prime n) (hk : u.multiplier = 2 ^ k)
(h_nlg2 : 2 < n) : applyCollatzKTimes u n (k + 1) = n := by
  unfold applyCollatzKTimes
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
  unfold applyCollatz
  have h_odd : Odd n := by
    apply Nat.Prime.odd_of_ne_two
    · exact h_nprime
    · exact Ne.symm (Nat.ne_of_lt h_nlg2)
  have h_neg_even := Nat.not_even_iff_odd.mpr h_odd
  simp_all only [reduceIte, isShapeUniverse, add_zero]
  exact applyCollatzKTimes_power_of_two_mul u n k


-- In shape universes with a multiplier which is even, but not a power of two,
-- where the multiplier is of the form k1 * 2 ^ k2, with k1 odd and greater than 1,
-- and k2 greater than 1, doing k2 steps multiplies the number by k1.
-- This theorem is for the odd case of n, we'll do the even case in the next theorem
theorem shapeUniversesWithEvenNonPowerOfTwoMultipliersMultiplyByOddPart (u : CollatzUniverse)
(h : isShapeUniverse u) (k1 k2 : ℕ) (hk : u.multiplier = k1 * 2 ^ k2)
(hk2_gt1 : k2 > 1) (n : ℕ) (h_odd : Odd n) :
applyCollatzKTimes u n (k2 + 1) = k1 * n := by
  unfold applyCollatzKTimes
  have : k2 ≠ 0 := Nat.ne_zero_of_lt hk2_gt1
  simp_all only [gt_iff_lt, ne_eq, ↓reduceIte, applyCollatz, ← Nat.not_even_iff_odd,
  isShapeUniverse, add_zero]
  have test := applyCollatzKTimes_pow_two_descent u k2  (n * k1) k2 (by rfl)
  grind only

-- Same as above, but for even this time.
theorem shapeUniversesWithEvenNonPowerOfTwoMultipliersMultiplyByOddPartEven (u : CollatzUniverse)
(h : isShapeUniverse u) (k1 k2 : ℕ) (hk : u.multiplier = k1 * 2 ^ k2)
(hk2_gt1 : k2 > 1) (n : ℕ) (h_even : Even n) :
applyCollatzKTimes u n (k2 + 1) = k1 * n := by
  unfold applyCollatzKTimes
  have : k2 ≠ 0 := Nat.ne_zero_of_lt hk2_gt1
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
  -- This one is significantly more difficult,
  -- as the odd number could be at any point in the trajectory
  sorry

-- All shape universes with multipliers which are even, but not a power of two,
-- explode nontrivially. At each multiply, it first divides as many times as the multiplier
-- is divisible by 2, and then multiplies by the odd part of the multiplier,
-- which is greater than 1.
theorem shapeUniversesWithEvenNonPowerOfTwoMultipliersAreUnbounded (u : CollatzUniverse)
(h : isShapeUniverse u) (k1 k2 : ℕ) (hk : u.multiplier = k1 * 2 ^ k2) (hk1_odd : Odd k1)
(hk1_gt1 : k1 > 1) (hk2_gt1 : k2 > 1) : isUnbounded u := by
  have : ¬ isBounded u ↔ isUnbounded u := by simp [boundedEqNotUnbounded]
  rw [← this]
  simp only [isBounded, not_forall, not_exists, not_le]
  use 1
  intro low
  use low + k2
  unfold applyCollatzKTimes applyCollatz
  have : k2 ≠ 0 := Nat.ne_zero_of_lt hk2_gt1
  simp_all only [isShapeUniverse, gt_iff_lt, ne_eq, Nat.add_eq_zero_iff, and_false,
    ↓reduceIte, Nat.not_even_one, mul_one, add_zero]
  have test := shapeUniversesWithEvenNonPowerOfTwoMultipliersMultiplyByOddPartEven
    u h k1 k2 hk hk2_gt1 (k1 * 2 ^ k2) (by grind)
  -- The test case operates on k2 + 1 iterations, but we are doing low + k2  -1 iterations.
  -- We split into two calls, one of which we can replace.
  have convert := applyCollatzKTimes_add u (k1 * 2 ^ k2) (k2 + 1) (low - 2)
  -- In order to simplify further, we need to consider if low is less than two.
  by_cases h : low < 2
  · -- We can simply show that the entire right side is at least 2.
    have right_ge_2 : 2 ≤ applyCollatzKTimes u (k1 * 2 ^ k2) (low + k2 - 1) := by
      sorry
    sorry
  sorry



-- End of shape universe theorems.

-- Helper theorem: If a collatz universe maps an odd number to an odd number,
-- then all odd numbers are mapped to odd numbers.
theorem oddToOddImpliesAllOddToOdd (u : CollatzUniverse) (h : ∃ n, Odd n ∧ Odd (applyCollatz u n)) :
∀ n, Odd n → Odd (applyCollatz u n) := by
  obtain ⟨n₀, h_n₀_odd, h_apply_n₀_odd⟩ := h
  intro n h_n_odd
  unfold applyCollatz at *;
  simp_all [← Nat.not_odd_iff_even]
  grind only [= Nat.not_odd_iff_even, = Nat.even_add, = Nat.even_mul]

-- When looking at the multiverse, it is visible that a checkerboard pattern emerges,
-- Where, if the parity of the multiplier and adder is different,
-- Odd numbers are sent to odd numbers.
def isCheckerboard (u : CollatzUniverse) : Prop :=
  (Even u.multiplier ∧ Odd u.adder) ∨ (Odd u.multiplier ∧ Even u.adder)

-- On a checkerboard universe, the sum of the multiplier and adder is odd.
lemma checkerboardImpliesSumOdd (u : CollatzUniverse) (h : isCheckerboard u) :
  Odd (u.multiplier + u.adder) := by
  grind only [isCheckerboard, = Nat.not_odd_iff_even, = Nat.odd_iff, = Nat.even_add, = Nat.even_iff]

-- On a checkerboard universe, 1 is sent to an odd number,
-- so all odd numbers are sent to odd numbers.
lemma checkerboardImpliesOneToOdd (u : CollatzUniverse) (h : isCheckerboard u) :
  Odd (applyCollatz u 1) := by
  unfold isCheckerboard at h
  unfold applyCollatz
  simp only [Nat.not_even_one, ↓reduceIte, mul_one]
  grind only [= Nat.even_iff, = Nat.not_odd_iff_even, = Nat.odd_iff, = Nat.even_add]

theorem checkerboardImpliesAllOddToOdd (u : CollatzUniverse) (h : isCheckerboard u) :
  ∀ n, Odd n → Odd (applyCollatz u n) := by
  have h_one_to_odd : Odd (applyCollatz u 1) := checkerboardImpliesOneToOdd u h
  apply oddToOddImpliesAllOddToOdd u
  use 1
  exact ⟨ by decide, h_one_to_odd ⟩

-- Even stronger, in a checkerboard universe, for all k, applying the Collatz function k times to an
-- odd number results in an odd number.
lemma checkerboardImpliesAllOddToOddKTimes (u : CollatzUniverse) (h : isCheckerboard u) :
  ∀ n k, Odd n → Odd (applyCollatzKTimes u n k) := by
  have h_all_odd_to_odd : ∀ n, Odd n → Odd (applyCollatz u n) := checkerboardImpliesAllOddToOdd u h
  intro n k h_n_odd
  induction k with
  | zero => simp only [applyCollatzKTimes_zero]; exact h_n_odd
  | succ m Hm =>
    rw [applyCollatzKTimes_add]
    rw [applyCollatzKTimes]
    simp [applyCollatzKTimes_zero]
    simp_all only

-- Helper theorem: With only a few exceptions, applying the Collatz function to an odd number
-- results in a larger number. (Expections: mult = 0 or (mult = 1 and adder = 0))
theorem oddStepGreater (u : CollatzUniverse)
  (h_n_exception : (u.multiplier ≠ 0) ∧ (u.multiplier ≠ 1 ∨ u.adder ≠ 0)) :
  ∀ n, Odd n → applyCollatz u n > n := by
  intro n h_n_odd
  unfold applyCollatz at *;
  simp only [Nat.not_even_iff_odd.mpr h_n_odd, ↓reduceIte]
  obtain ⟨mult_gt0, h_mult_exception⟩ := h_n_exception
  have n_gt0 : n > 0 := Odd.pos h_n_odd
  have h_mult_mul_n_ge_n: u.multiplier * n ≥ n := by
    have h_mult_ge_1 : u.multiplier ≥ 1 := Nat.one_le_iff_ne_zero.mpr mult_gt0
    exact Nat.le_mul_of_pos_left n h_mult_ge_1
  by_cases h : u.adder = 0
  · have : u.multiplier > 1 := by
      grind only
    simp_all only [ne_eq, not_true_eq_false, or_false, gt_iff_lt, ge_iff_le, le_mul_iff_one_le_left,
      add_zero, lt_mul_iff_one_lt_left]
  · have : u.adder > 0 := by
      exact Nat.pos_of_ne_zero h
    exact lt_add_of_le_of_pos h_mult_mul_n_ge_n this



-- If a universe is checkerboard, the universe is unbounded.
-- This is because any odd number stays odd after applying the Collatz function.
theorem checkerboardUnbounded (u : CollatzUniverse) (h : isCheckerboard u)
  (h0_neq_m : u.multiplier ≠ 0) (h0_neq_a : u.adder ≠ 0) : isUnbounded u := by
  -- We will again focus on 1 as the starting number.
  -- We show that applying the Collatz function k times always results in an odd number.
  have h_odd : ∀ k, Odd (applyCollatzKTimes u 1 k) := by
    have := checkerboardImpliesAllOddToOddKTimes u h 1
    simp_all only [odd_one, forall_const]
  -- These universes are runaway,
  -- since the odd numbers just keep getting multiplied by the multiplier.
  have : isRunaway' u := by
    unfold isRunaway'
    use 1
    intro k
    set inner := applyCollatzKTimes u 1 k
    rw [applyCollatzKTimes_add]
    unfold applyCollatzKTimes
    simp only [one_ne_zero, ↓reduceIte, tsub_self, applyCollatzKTimes_zero, gt_iff_lt]
    have h_inner_odd : Odd inner := h_odd k
    have h_odd_greater := oddStepGreater u ⟨ h0_neq_m, Decidable.not_or_of_imp fun a ↦ h0_neq_a ⟩
      inner h_inner_odd
    exact Nat.lt_of_succ_le h_odd_greater
  rw [← runawayIffRunaway' u ] at this
  exact runawayIffUnbounded u this
