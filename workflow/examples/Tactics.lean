import Mathlib.Tactic
import Aesop

/-! Small environment examples, separate from AgentUCT's mathematical claims. -/

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by aesop

example (x y : ℝ) (h : x ≤ y) : x + 1 ≤ y + 1 := by linarith

example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by omega

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring
