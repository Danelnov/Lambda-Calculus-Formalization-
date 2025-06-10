import Lambda.Defs
import Mathlib.Tactic.Ring
open Lambda

theorem unshift_var_le {c i n : Nat} :
  c ≤ n → unshift c i (var n) = var (n - i) := by
  intro h
  unfold unshift
  have nnltc : ¬ (n < c) := by omega
  simp [nnltc]

theorem unshift_var_lt {c i n : Nat} : n < c → (↓) c i n = var n := by
  intro h; unfold unshift; simp [h]

theorem shift_zero {N : Lambda} : ∀ {c}, (↑) c 0 N = N := by
  induction N with
  | var n => intro; simp
  | app N₁ N₂ ih₁ ih₂ => intro; simp [ih₁, ih₂]
  | abs M ih => intro; simp [ih]

theorem shift_add' (N : Lambda) :
  ∀ {c i₁ i₂ : Nat}, (↑) c i₁ ((↑) c i₂ N) = (↑) c (i₁ + i₂) N := by
  induction N with
  | var n => intro; repeat (first | omega | simp | split_ifs)
  | app N₁ N₂ ih₁ ih₂ => intro; simp [ih₁, ih₂]
  | abs M ih => intro; simp [ih]

@[simp]
theorem shift_add (n m : Nat) (N : Lambda)
  : ∀ (i j : Nat), i ≤ j → j ≤ i + m → (↑) j n ((↑) i m N) = (↑) i (m + n) N := by
  induction N with
  | var k => intros; repeat (first | omega | simp | split_ifs)
  | app e v ihe ihv =>
    intros; simp; constructor <;> (first | apply ihe | apply ihv) <;> omega
  | abs e ih => intros; simp; apply ih <;> omega

@[simp]
theorem subst_gt_range {M : Lambda} : ∀ {N n}, n > range M → M[n := N] = M := by
  induction M with
  | var m =>
    intro _ _ h; unfold range at h
    simp; intro; omega
  | app M₁ M₂ ih1 ih2 =>
    intro _ _ h
    unfold range at h
    have ⟨ngt1, ngt2⟩ := Nat.max_lt.mp h
    simp [ih1 ngt1, ih2 ngt2]
  | abs M ih => intro _ _ h; simp [subst, ih (Nat.lt_add_right 1 h)]

theorem gt_range_gt_shift {N : Lambda} :
  ∀ {n i j}, n > range N → n + j > range ((↑) i j N) := by
  induction N with
  | var m => intros; simp_all; split_ifs <;> simp <;> omega
  | app N₁ N₂ ih1 ih2 => intros; simp_all
  | abs N ih => intro _ _ _ h; simp [ih h]

@[simp]
theorem shift_unshift_id (M : Lambda) (c i : Nat) : (↓) (c + i) i ((↑) c i M) = M := by
  induction M generalizing c with
  | var n => repeat (first | simp | split_ifs | omega)
  | app M₁ M₂ ih1 ih2 => simp [ih1, ih2]
  | abs M ih =>
    simp; rw [Nat.add_assoc, Nat.add_comm i 1, ← Nat.add_assoc]; exact ih (c + 1)

theorem shift_subst  (M : Lambda) (k j i : Nat) (klej : k ≤ j) (L : Lambda) :
  (↑) k i (M[j := L]) = ((↑) k i M)[j + i := L] := by
  induction M generalizing k j with
  | var n => repeat (first | simp | split_ifs | omega | apply shift_add)
  | app M₁ M₂ ih1 ih2 =>
    simp [ih1, ih2]
    constructor <;> (first | apply ih1 | apply ih2) <;> assumption
  | abs M ih =>
    simp
    rw [Nat.add_assoc, Nat.add_comm i 1, ← Nat.add_assoc]
    apply ih
    exact Nat.add_le_add_right klej 1

@[simp]
theorem shift_subst_eq_shift (M N : Lambda) (k i j : Nat) :
  k ≤ i → i < k + (j + 1) → (↑) k j M = ((↑) k (j + 1) M)[i := N] := by
  induction M generalizing k i with
  | var n => repeat (first | simp | split_ifs | omega)
  | app M₁ M₂ ih1 ih2 =>
    intro klei ileji
    simp
    constructor <;> (first | apply ih1 | apply ih2) <;> assumption
  | abs M ih =>
    intro klei ileji
    simp
    apply ih
    exact Nat.add_le_add_right klei 1
    have : i + 1 < k + (j + 1) + 1 := Nat.add_lt_add_right ileji 1
    ring_nf at this
    ring_nf
    assumption

theorem substitution (M N L : Lambda) (n m : Nat) (nlem : n ≤ m) :
  M[n := N][m := L] = M[m + 1 := L][n := N[m - n := L]] := by
  induction M generalizing n m with
  | var k =>
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
      have k_gt_0 := Nat.zero_lt_of_lt kgtn
      rcases Nat.lt_trichotomy (k - 1) m with k1_le_m | rfl | k1_gt_m
      -- * Case k - 1 < m
      . simp [k1_le_m]
        have k_le_m1 : k < m + 1 := by
          exact (Nat.sub_lt_iff_lt_add k_gt_0).mp k1_le_m
        simp [k_le_m1, nklen, knen]
      -- * Case k - 1 = m
      . have k_eq : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.zero_lt_of_lt kgtn)
        simp [k_eq]
        have ⟨m, hm⟩: ∃ m : Nat, k = m + 1 := Nat.exists_eq_add_one.mpr k_gt_0
        simp [hm]
        apply shift_subst_eq_shift
        exact Nat.zero_le n
        rw [← hm, Nat.zero_add]
        assumption
      -- * Case k - 1 > m
      . have k_gt_m1 : k > m + 1 := Nat.add_lt_of_lt_sub k1_gt_m
        have n_k1_le_m : ¬ (k - 1 < m) := Nat.not_lt_of_gt k1_gt_m
        have m_ne_kp1 : m ≠ k - 1 := Nat.ne_of_lt k1_gt_m
        have n_k_le_m1 : ¬ (k < m + 1) := Nat.not_lt_of_gt k_gt_m1
        have m1_ne_k : m + 1 ≠ k := (Nat.ne_of_lt k_gt_m1)
        have : n < k - 1 := Nat.lt_of_le_of_lt nlem k1_gt_m
        have nkp1_le_n : ¬ (k - 1 < n) := by exact Nat.not_lt_of_gt this
        simp [n_k1_le_m, m_ne_kp1, n_k_le_m1, m1_ne_k, nkp1_le_n]
        intro n_eq_km1
        rw [n_eq_km1] at this
        have : k - 1 ≠ k - 1 := Nat.ne_of_lt this
        contradiction
  | app M₁ M₂ ih1 ih2 =>
    simp
    constructor <;> (first | apply ih1 | apply ih2) <;> assumption
  | abs M ih =>
    have := ih (n + 1) (m + 1) (Nat.add_le_add_right nlem 1)
    rw [Nat.add_sub_add_right m 1 n] at this
    simp_all
