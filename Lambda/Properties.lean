import Lambda.Defs
-- import Mathlib.Tactic
open Lambda

theorem add_ne_of_ne (a b c : Nat) : a ≠ b → a + c ≠ b + c := by
  intro h
  rcases Nat.lt_or_gt_of_ne h with aleb | agtb
  -- * Case a < b
  . exact Nat.ne_of_lt <| Nat.add_lt_add_right aleb c
  . exact Nat.ne_of_gt <| Nat.add_lt_add_right agtb c

theorem shift_var_le {c i n : Nat} : c ≤ n → (↑) c i n = var (n + i) := by
  intro h
  unfold shift
  have nnltc : ¬ (n < c) := Nat.not_lt.mpr h
  simp [nnltc]

theorem shift_var_lt {c i n : Nat} : n < c → (↑) c i n = var n := by
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
    unfold shift; simp [ih₁, ih₂]
  | abs M ih =>
    intro c
    unfold shift; simp [ih]


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
  : ∀ (i j : Nat), i ≤ j → j ≤ i + m → (↑) j n ((↑) i m N) = (↑) i (m + n) N
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

@[simp]
theorem subst_gt_range {M} : ∀ {N n}, n > range M → M[n := N] = M := by
  induction M with
  | var m =>
    intro N n h
    unfold range at h
    simp [Nat.ne_of_lt h]
    intro nlem
    have : n < n := Nat.lt_of_le_of_lt nlem h
    have : n ≠ n := Nat.ne_of_lt this
    contradiction
  | app M₁ M₂ ih1 ih2 =>
    intro N n h
    unfold range at h
    have ⟨ngt1, ngt2⟩ := Nat.max_lt.mp h
    simp [ih1 ngt1, ih2 ngt2]
  | abs M ih =>
    intro N n h
    unfold range at h
    have : n + 1 > M.range := Nat.lt_add_right 1 h
    simp [ih this]


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
    simp [@ih n (i + 1) j h]


@[simp]
theorem shift_unshift_id (M : Lambda) (c i : Nat) : (↓) (c + i) i ((↑) c i M) = M := by
  revert c
  induction M with
  | var n =>
    intro c
    simp
    rcases Nat.lt_trichotomy n c with nlec | rfl | ngtc
    -- * Case n < c
    . simp [nlec]
      intro cilen
      have : n < c + i := Nat.lt_add_right i nlec
      have : c + i < c + i := Nat.lt_of_le_of_lt cilen this
      have ncileci : ¬ (c + i < c + i) := Nat.lt_irrefl (c + i)
      contradiction
    -- * Case n = c
    . simp
    -- * Case n > c
    . have : ¬(n < c) := Nat.not_lt_of_gt ngtc
      simp [this]
  | app M₁ M₂ ih1 ih2 =>
    intro c
    simp
    constructor <;> first | exact ih1 c | exact ih2 c
  | abs M ih =>
    intro c
    simp
    rw [Nat.add_assoc, Nat.add_comm i 1, ← Nat.add_assoc]
    exact ih (c + 1)

theorem shift_subst  (M : Lambda) (k j i : Nat) (klej : k ≤ j) (L : Lambda) :
  (↑) k i (M[j := L]) = ((↑) k i M)[j + i := L] := by
  revert k j
  induction M with
  | var n =>
    intro k j klej
    rcases Nat.lt_trichotomy n k with nlek | rfl | ngtk
    -- * Case n < k
    . have nlej : n < j := Nat.lt_of_lt_of_le nlek klej
      have nlejp1 : n < j + i := Nat.lt_add_right i nlej
      simp [nlej, nlek, nlejp1]
    -- * Case n = k
    . rcases Or.symm (Nat.eq_or_lt_of_le klej) with nlej | rfl
      -- * Case n < j
      . simp [nlej]
      -- * Case n = j
      . simp
        apply shift_add <;> simp
    -- * Case n > k
    . have nnlek : ¬ (n < k) := Nat.not_lt_of_gt ngtk
      rcases Nat.lt_trichotomy n j with nlej | rfl | ngtj
      -- * Case n < j
      . simp [nlej, nnlek]
      -- * Case n = j
      . simp [nnlek]
        apply shift_add <;> simp ; assumption
      -- * Case n > j
      . have nnlej : ¬ (n < j) := Nat.not_lt_of_gt ngtj
        have nnej : j ≠ n := Nat.ne_of_lt ngtj
        have : ¬ (n - 1 < k) := by
          intro h
          apply Nat.lt_irrefl (n - 1)
          apply Nat.lt_of_lt_of_le h
          exact Nat.le_sub_one_of_lt ngtk
        simp [nnlej, nnej, nnlek, this]
        rw [Nat.sub_add_comm]
        exact (Nat.zero_lt_of_lt ngtk)
  | app M₁ M₂ ih1 ih2 =>
    intro k j klej
    simp
    constructor <;> (first | apply ih1 | apply ih2) <;> assumption
  | abs M ih =>
    intro k j klej
    simp
    rw [Nat.add_assoc, Nat.add_comm i 1, ← Nat.add_assoc]
    apply ih
    exact Nat.add_le_add_right klej 1


theorem shift_subst_eq_shift (M N : Lambda) (k i j : Nat) :
  k ≤ i → i < k + (j + i) → ((↑) k (j + 1) M)[i := N] = (↑) k j M := by
  revert k i
  induction M with
  | var n =>
    intro k i klei ileji
    rcases Nat.lt_trichotomy n k with nlek | rfl | ngtk
    -- * Case n < k
    . have nlei : n < i := Nat.lt_of_lt_of_le nlek klei
      have inen : i ≠ n := Ne.symm (Nat.ne_of_lt nlei)
      simp [nlek, inen]
      intro ilen
      have : n < n := Nat.lt_of_lt_of_le nlei ilen
      have : n ≠ n := Nat.ne_of_lt this
      contradiction
    -- * Case n = k
    . simp
      rcases Nat.lt_trichotomy (n + (j + 1)) i with mlei | rfl | mgti
      -- * Case m < i
      . sorry
      sorry
      sorry
    sorry
    | app M₁ M₂ ih1 ih2 =>
      sorry
    | abs M ih =>
      sorry

theorem substitution (M N L : Lambda) (n m : Nat) :
  n ≤ m → M[n := N][m := L] = M[m + 1 := L][n := N[m - n := L]] := by
  revert n m
  induction M with
  | var k =>
    intro n m nlem
    rcases Nat.lt_trichotomy k n with klen | rfl |kgtn
    -- * Case k < n
    . have n_gt_range_k : n > range k := klen
      have m_gt_range_k : m > range k := Nat.lt_of_lt_of_le klen nlem
      have m1_gt_range_k : m + 1 > range k := Nat.lt_add_right 1 m_gt_range_k
      simp_all only [subst_gt_range]
    -- * Case k = n
    . have k_le_m1 : k < m + 1 := by exact Nat.lt_add_one_of_le nlem
      simp [k_le_m1]
      apply Eq.symm
      have zero_le_mmk : 0 ≤ m - k := (Nat.le_sub_iff_add_le' nlem).mpr nlem
      have := shift_subst N 0 (m -k) k zero_le_mmk L
      have m_eq : m - k + k = m := Nat.sub_add_cancel nlem
      rw [m_eq] at this
      assumption
    -- * Case k > n
    . have nklen : ¬ (k < n) := Nat.not_lt_of_gt kgtn
      have knen : n ≠ k := Nat.ne_of_lt kgtn
      simp [nklen, knen]

      rcases Nat.lt_trichotomy (k - 1) m with k1_le_m | rfl | k1_gt_m
      -- * Case k - 1 < m
      . simp [k1_le_m]
        have k_le_m1 : k < m + 1 := sorry
        simp [k_le_m1, nklen, knen]
      -- * Case k - 1 = m
      . have k_eq : k - 1 + 1 = k := sorry
        simp [k_eq]
        sorry
      -- * Case k - 1 > m
      . sorry
  | app M₁ M₂ ih1 ih2 =>
    intros
    simp
    constructor <;> (first | apply ih1 | apply ih2) <;> assumption
  | abs M ih =>
    intro n m nlem
    have := ih (n + 1) (m + 1) (Nat.add_le_add_right nlem 1)
    rw [Nat.add_sub_add_right m 1 n] at this
    simp_all
