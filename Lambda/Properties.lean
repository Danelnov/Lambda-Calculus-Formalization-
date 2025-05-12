import Lambda.Defs
open Lambda

theorem shift_var_le {c i n : Nat}  : c ≤ n → (↑) c i n = n + i := by
  intro h
  unfold shift
  have nnltc : ¬ (n < c) := Nat.not_lt.mpr h
  simp [nnltc]

theorem shift_var_lt {c i n : Nat} : n < c → (↑) c i n = n := by
  intro h; unfold shift; simp [h]

theorem unshift_var_le {c i n : Nat} :
  c ≤ n → unshift c i (var n) = var (n - i) := by
  intro h
  unfold unshift
  have nnltc : ¬ (n < c) := Nat.not_lt.mpr h
  simp [nnltc]

theorem unshift_var_lt {c i n : Nat} : n < c → (↓) c i n = var n := by
  intro h; unfold unshift; simp [h]

theorem shift_zero {N : Lambda} : ∀ {c}, (↑) c 0 N = N := by
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


theorem shift_add' (N : Lambda) :
  ∀ {c i₁ i₂ : Nat}, (↑) c i₁ ((↑) c i₂ N) = (↑) c (i₁ + i₂) N := by
  induction N with
  | var n =>
    intro c i₁ i₂
    by_cases h : n < c
    . simp [shift_var_lt h, h]
    . have clen : c ≤ n := Nat.le_of_not_lt h
      simp [h, shift_var_le <| Nat.le_add_right_of_le clen]
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

-- * ∀ (i j : Nat), i ≤ j → j ≤ i + m → ↑ j n (↑ i m N) = ↑ i (m + n) N
theorem shift_add (n m : Nat) (N : Lambda)
  : ∀ (i j : Nat), i ≤ j → j ≤ i + m → (N.shift i m).shift j n = N.shift i (m + n)
  := by
  induction N with
  | var k =>
    intro i j ilej jlem1
    simp_all [Lambda.shift]
    rcases Nat.lt_trichotomy k i with klei | rfl | kgti
    -- * Case k < i
    . simp [klei]
      intro h
      have : j < i := Nat.lt_of_le_of_lt h klei
      have : j < j := Nat.lt_of_lt_of_le this ilej
      have : ¬ j < j := Nat.lt_irrefl j
      contradiction
    -- * Case k = i
    . simp [Nat.not_lt.mpr jlem1]; ac_nf
    -- * Case k > i
    . have : i + m < k + m := Nat.add_lt_add_right kgti m
      have : j < k + m := Nat.lt_of_le_of_lt jlem1 this
      have : ¬ k + m < j := Nat.not_lt_of_gt this
      simp [Nat.not_lt_of_gt kgti, this]
      ac_nf
  | app e v ihe ihv =>
    intro i j ilej jlemi
    simp_all
  | abs e ih =>
    intro i j ilej jleim
    simp_all
    apply ih
    exact Nat.add_le_add_right ilej 1
    rw [Nat.add_assoc, Nat.add_comm 1 m, ← Nat.add_assoc]
    exact Nat.add_le_add_right jleim 1

-- (↑) 0 1 ((↑) i j L) =

theorem shift_subst (N : Lambda) :
  ∀ {n i j L}, i ≤ n → (↑) i j (N[n ↦ L]) = ((↑) i j N)[n + j ↦ (↑) i j L] := by
  induction N with
  | var m =>
    intro n i j L ilen
    simp
    rcases Nat.lt_trichotomy m i with mlei | rfl | mgti
    -- * Case m < i
    . have nlen : m < n := Nat.lt_of_lt_of_le mlei ilen
      have mlenj : m < n + j := Nat.lt_add_right j nlen
      have mneqnj : m ≠ n + j := by exact Nat.ne_of_lt mlenj
      simp [Nat.ne_of_lt nlen, mlei, mneqnj]
    -- * Case m = j
    . by_cases hmn : m = n
      -- * Sub Case m = n
      . simp [hmn]
      -- * Sub Case m ≠ n
      . simp [hmn]
    -- * Case m > j
    . simp [Nat.not_lt_of_gt mgti]
      by_cases hmn : m = n
      -- * Sub case m = n
      . simp [hmn]
      -- * Sub case m ≠ n
      . simp [hmn]
        intro mlei
        have mlem : m < m := Nat.lt_trans mlei mgti
        have : ¬ m < m := Nat.lt_irrefl m
        contradiction
    | app N₁ N₂ ih1 ih2 =>
      intro n i j L ilen
      simp <;> repeat (first | constructor | exact ih1 ilen | exact ih2 ilen )
    | abs N ih =>
      intro n i j L ilen
      have : i + 1 ≤ n + 1 := Nat.add_le_add_right ilen 1
      simp
      sorry

theorem subst_gt_range {M} : ∀ {N n}, n > range M → M[n ↦ N] = M := by
  induction M with
  | var m =>
    intro N n h
    unfold range at h
    simp [Nat.ne_of_lt h]
  | app M₁ M₂ ih1 ih2 =>
    intro N n h
    unfold range at h
    have ⟨ngt1, ngt2⟩ := Nat.max_lt.mp h
    simp [ih1 ngt1, ih2 ngt2]
  | abs M ih =>
    intro N n h
    unfold range at h
    have ngtrm1 : n + 1 > range M := Nat.lt_of_succ_lt <| Nat.lt_add_right 1 h
    simp  [ih ngtrm1]

theorem gt_range_gt_shift {N : Lambda} :
  ∀ {n i j}, n > range N → n + j > range ((↑) i j N) := by
  induction N with
  | var m =>
    intro n i j h
    unfold range at h
    simp [shift]
    by_cases mi : m < i
    -- * case m < i
    . simp [mi, Nat.lt_add_right j h]
    -- * Case ¬ m < i
    . simp [mi, h]
  | app N₁ N₂ ih1 ih2 =>
    intro n i j h
    unfold range at h
    have ⟨ngt1, ngt2⟩ := Nat.max_lt.mp h
    unfold shift range
    apply Nat.max_lt.mpr
    constructor <;> repeat (first | apply ih1 | apply ih2 | assumption)
  | abs N ih =>
    intro n i j h
    unfold range at h
    have : n - 1 > range N := Nat.lt_sub_of_add_lt h
    have := @ih (n - 1) (i + 1) j this
    have : n + j > ((↑) (i + 1) j N).range + 1 := by sorry
    simp [shift, range]
    assumption

theorem sustitution {M N L: Lambda} :
  ∀ {n m N L}, n ≠ m → n > range L → M[n ↦ N][m ↦ L] = M[m ↦ L][n ↦ N[m ↦ L]] := by
  induction M with
  | var k =>
    intro n m N L mneqn ngtrl
    by_cases h : k = n
    -- * Case k = m
    . simp [h, mneqn]
    -- * case k ≠ m
    . simp [h]
      by_cases h' : k = m
      -- * case k = m
      . simp [h', subst_gt_range ngtrl]
      -- * Case k ≠ m
      . simp [h', h]
  | app M₁ M₂ ih1 ih2 =>
    intro n m N L nneqm ngtrl
    simp [ih1 nneqm ngtrl, ih2 nneqm ngtrl]
  | abs M ih =>
    intro n m N L nneqm ngtrl
    have h1 : n + 1 ≠ m + 1 := by sorry
    have : n + 1 > range ((↑) 0 1 L) := gt_range_gt_shift ngtrl
    have := @ih (n + 1) (m + 1) ((↑) 0 1 N) ((↑) 0 1 L) h1 this
    simp
    sorry
