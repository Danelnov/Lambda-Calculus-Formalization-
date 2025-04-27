import Lambda.Defs
open Lambda

theorem shift_var_le {c i n : Nat}  : c ≤ n → shift c i (var n) = var (n + i) := by
  intro h
  unfold shift
  have nnltc : ¬ (n < c) := Nat.not_lt.mpr h
  simp [nnltc]

theorem shift_var_lt {c i n : Nat} : n < c → shift c i (var n) = var n := by
  intro h; unfold shift; simp [h]

theorem unshift_var_le {c i n : Nat} :
  c ≤ n → unshift c i (var n) = var (n - i) := by
  intro h
  unfold unshift
  have nnltc : ¬ (n < c) := Nat.not_lt.mpr h
  simp [nnltc]

theorem unshift_var_lt {c i n : Nat} : n < c → unshift c i (var n) = var n := by
  intro h; unfold unshift; simp [h]

theorem shift_zero {N : Lambda} : ∀ {c}, shift c 0 N = N := by
  induction N with
  | var n =>
    intro c
    by_cases h : c ≤ n
    . exact shift_var_le h
    . exact shift_var_lt <| Nat.not_le.mp h
  | app N₁ N₂ ih₁ ih₂ =>
    intro
    unfold shift <;> simp [ih₁, ih₂]
  | abs M ih =>
    intro c
    unfold shift <;> simp [ih]


theorem shift_add {N : Lambda} :
  ∀ {c i₁ i₂ : Nat}, shift c i₁ (shift c i₂ N) = shift c (i₁ + i₂) N := by
  induction N with
  | var n =>
    intro c i₁ i₂
    by_cases h : n < c
    . simp [shift_var_lt h]
    . have clen : c ≤ n := Nat.le_of_not_lt h
      simp_all [shift_var_le clen, shift_var_le <| Nat.le_add_right_of_le clen]
      ac_nf
  | app N₁ N₂ ih₁ ih₂ =>
    intro c i₁ i₂
    rw [shift]
    unfold shift
    simp [ih₁, ih₂]
  | abs M ih =>
    intro c i₁ i₂
    rw [shift]
    unfold shift
    simp [ih]
