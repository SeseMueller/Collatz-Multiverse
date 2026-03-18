import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Use

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
theorem oddNumbersSentToSameNumber (u : CollatzUniverse) (n : ℕ) (h : isHubAndSpoke u)
(hn : Odd n) : applyCollatz u n = u.adder := by
  unfold applyCollatz
  unfold isHubAndSpoke at h
  simp [h, hn]

-- Maybe I can also prove that in a Hub-and-Spoke universe, all numbers eventually end up
-- at the adder, but I will save that for later.

-- TODO: maybe prove the bi-angle or tri-angle nature of hub-and-spoke universes
-- with an adder which is a power of 2?

-- TODO: Prove the statement about period doubling in the Hub-and-Spoke universes


-- We call a universe with an adder of 0 a "Shape Universe", since all multipliers which are
-- a power of 2 give rise to shapes with log_2(n) sides (or more precisely, edges).
def isShapeUniverse (u : CollatzUniverse) : Prop :=
  u.adder = 0

-- We call a universe "bounded", if for all nubers, there exists a k and N such that
-- applying the Collatz function k times to the number results in a number
-- less than or equal to N.
def isBounded (u : CollatzUniverse) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ k : ℕ, applyCollatzKTimes u n k ≤ N
-- This means that all numbers eventually end up in a cycle, and that there are no
-- divergent trajectories. However, it does not limit the size or number of the cycles.
-- Also note that this does not mean that the cycle needs to include, or even include
-- or contain lower numbers than the starting number.

-- It is enough to show that there is some k for which all n do not grow.
theorem isBoundedIfPathGoesLower: (∀ n : ℕ, ∃ k : ℕ, applyCollatzKTimes u n k ≤ n)
  → isBounded u := by
  simp only [isBounded]
  intro h n
  specialize h n
  obtain ⟨k, hk⟩ := h
  sorry

-- We can show that the Shape Universes with a multiplier which is a power of 2 are bounded.
theorem shapeUniversesWithPowerOfTwoMultipliersAreBounded (u : CollatzUniverse)
(h : isShapeUniverse u) (m : ∃ k : ℕ, u.multiplier = 2 ^ k) : isBounded u := by
  unfold isShapeUniverse at h
  unfold isBounded
  intro n
  obtain ⟨k, m⟩ := m

  -- unfold applyCollatzKTimes

  use n * u.multiplier
  -- ?


  sorry



-- The opposite of a bounded universe is an "unbounded" universe, where there exists a number
-- such that for all k, applying the Collatz function k times to the number results in a number
-- greater than the original number.
def isUnbounded (u : CollatzUniverse) : Prop :=
  ∃ n : ℕ, ∀ N : ℕ, ∃ k, applyCollatzKTimes u n k > N

theorem boundedEqNotUnbounded (u : CollatzUniverse) : isBounded u ↔ ¬ isUnbounded u := by
  simp [isBounded, isUnbounded]

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
theorem shapeUniversesWithOddLargerTwoAreUnbounded (u : CollatzUniverse) (h: isShapeUniverse u)
(hodd : Odd u.multiplier ) (hgt2 : u.multiplier > 2): isUnbounded u := by

  have : ¬ isBounded u ↔ isUnbounded u := by simp [boundedEqNotUnbounded]
  rw [← this]
  -- Use the approach Aristotle used.

  -- unfold isUnbounded
  -- use 1
  -- intro N
  -- let mult := u.multiplier
  -- let magic : ℕ := (Nat.clog mult N) + 1
  -- use magic
  -- have applied := shapeUniversesWithOddLargeTwoGrowExponentially u h hodd 1 (magic) (odd_one)
  -- rw [applied]
  -- simp only [one_mul, gt_iff_lt]

  -- unfold magic
  -- have : 1 < mult := Nat.lt_of_add_left_lt hgt2
  -- have temp := Nat.le_pow_clog this N
  -- convert_to N < mult ^ (Nat.clog u.multiplier N) * mult
