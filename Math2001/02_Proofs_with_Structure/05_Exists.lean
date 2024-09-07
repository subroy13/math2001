/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  {
    have hxt': 0 < x * (-t) :=
      calc
        0 < (-x) * t := by addarith [hxt]
        _ = x * (-t) := by ring
    cancel x at hxt'
    have ht' : 0 > t := by addarith [hxt']
    apply ne_of_lt
    apply ht'
  }

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2
  constructor
  {
    calc
      p = p/2 + p/2 := by ring
      _ < p/2 + q/2 := by rel[h]
      _ = (p + q)/2 := by ring
  }
  {
    calc
      (p + q)/2 = p/2 + q/2 := by ring
      _ < q/2 + q/2 := by rel[h]
      _ = q := by ring
  }


example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt x 0
  obtain hx | hx := H
  {
    use 1
    calc
     1 ^ 2 = 1 := by numbers
     _ > x := by addarith [hx]
  }
  {
    use x + 1
    calc
      (x + 1) ^ 2 = x ^ 2 + 1 + x + x := by ring
      _ > x := by extra
  }



example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have H :=
    calc
      0 < a + t - (a * t + 1) := by addarith [ha]
      _ = (a - 1) * (1 - t) := by ring
  have H1 :=
    calc
      0 < (a - 1) * (1 - t) := by addarith [H]
      _ = (1 - a) * (t - 1) := by ring
  have H2 := le_or_gt a 1
  obtain ha1 | ha1 := H2
  {
    have H4 : 0 ≤ (1 - a) := by addarith [ha1]
    cancel (1 - a) at H1
    apply ne_of_gt
    addarith [H1]
  }
  {
    have H4 : 0  < (a - 1) := by addarith [ha1]
    cancel (a - 1) at H
    apply ne_of_lt
    addarith [H]
  }



example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  have h1 := le_or_succ_le a 2
  obtain ha1 | ha1 := h1
  {
    apply ne_of_lt
    calc
      m = 2 * a := by rw [ha]
      _ ≤ 2 * 2 := by rel[ha1]
      _ < 5 := by numbers
  }
  {
    apply ne_of_gt
    calc
      m = 2 * a := by rw [ha]
      _ ≥ 2 * 3 := by rel[ha1]
      _ > 5 := by numbers
  }

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  have H := le_or_succ_le n 0
  obtain hn | hn := H
  {
    use 2
    have hn1 := calc
      n * 2 + 7 ≤ 0 * 2 + 7 := by rel[hn]
      _ < 2 * 2 ^ 3 := by numbers
    addarith [hn1]
  }
  {
    use n + 2
    calc
      2 * (n + 2)^3 = 2 * n^3 + 12 * n^2 + 24 * n + 16 := by ring
      _ = n * (n + 2) + 7 + (2 * n^3 + 11 * n^2 + 22 * n + 9) := by ring
      _ ≥ n * (n + 2) + 7 := by extra
  }



example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a)/2, (a + c - b)/2, (a + b - c)/2
  constructor
  addarith [ha]
  constructor
  addarith [hb]
  constructor
  addarith [hc]
  constructor
  ring
  constructor
  ring
  ring
