/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h1, h2⟩ := hp'
  calc
    p ≥ -3 := by rel[h1]
    _ ≥ -5 := by numbers

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra
  have h3 : b^2 = 0 := by addarith[h1, h2]
  constructor
  {
    cancel 2 at h2
  }
  {
    cancel 2 at h3
  }

/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * a + b = (a + b) + a := by ring
    _ ≤ 3 + 1 := by rel[h1, h2]
    _ = 4 := by ring

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2 * r = (r + s) + (r - s) := by ring
    _ ≤ 1 + 5 := by rel[h1, h2]
    _ = 6 := by ring

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  have h3 : m + 5 ≤ 8 :=
    calc
      m + 5 ≤ n := by rel[h2]
      _ ≤ 8 := by rel[h1]
  addarith[h3]


example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h1 : p ≥ 7 := by addarith[hp]
  constructor
  {
    calc
      p^2 ≥ 7^2 := by rel[h1]
      _ = 49 := by ring
  }
  {
    apply h1
  }

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h1 : a ≥ 6 := by addarith[h]
  constructor
  {
    apply h1
  }
  {
    calc
      3 * a ≥ 3 * 6 := by rel[h1]
      _ ≥ 10 := by numbers
  }

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  have h3 : x = 3 :=
    calc
      x = 2 * (x + y)  - (x + 2 * y) := by ring
      _ = 2 * 5 - 7 := by rw[h1, h2]
      _ = 3 := by ring
  constructor
  {
    apply h3
  }
  {
    addarith[h1, h3]
  }

example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
    have h3 :=
      calc
        a * (b - 1) = a * b - a := by ring
        _ = 0 := by addarith[h1]
    have h4 := eq_zero_or_eq_zero_of_mul_eq_zero h3
    obtain h5 | h5 := h4
    {
      left
      constructor
      {
        apply h5
      }
      {
        calc
          b = a * b := by rw[h2]
          _ = 0 * b := by rw[h5]
          _ = 0 := by ring
      }
    }
    {
      right
      have h6 : b = 1 := by addarith[h5]
      constructor
      {
        calc
          a = a * 1 := by ring
          _ = a * b := by rw[h6]
          _ = b := by rw[h2]
          _ = 1 := by rw[h6]
      }
      {
        apply h6
      }
    }
