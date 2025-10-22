import Lambda.Defs
import Mathlib.Tactic.Ring
open Lambda

lemma unshift_var_le {c i n : Nat} :
  c ≤ n → (↓) c i (var n) = var (n - i) := by
  intro h
  unfold unshift
  have nnltc : ¬ (n < c) := by omega
  simp [nnltc]

lemma unshift_var_lt {c i n : Nat} : n < c → (↓) c i n = var n := by
  intro h; unfold unshift; simp [h]

@[simp]
lemma shift_zero {N : Lambda} : ∀ {c}, (↑) c 0 N = N := by
  induction N with
  | var n => intro; simp
  | app N₁ N₂ ih₁ ih₂ => intro; simp [ih₁, ih₂]
  | abs M ih => intro; simp [ih]

lemma shift_add' (N : Lambda) :
  ∀ {c i₁ i₂ : Nat}, (↑) c i₁ ((↑) c i₂ N) = (↑) c (i₁ + i₂) N := by
  induction N with
  | var n => intro; repeat (first | omega | simp | split_ifs)
  | app N₁ N₂ ih₁ ih₂ => intro; simp [ih₁, ih₂]
  | abs M ih => intro; simp [ih]

@[simp]
lemma shift_add (n m : Nat) (N : Lambda)
  : ∀ (i j : Nat), i ≤ j → j ≤ i + m → (↑) j n ((↑) i m N) = (↑) i (m + n) N := by
  induction N with
  | var k => intros; repeat (first | omega | simp | split_ifs)
  | app e v ihe ihv =>
    intros; simp; constructor <;> (first | apply ihe | apply ihv) <;> omega
  | abs e ih => intros; simp; apply ih <;> omega

@[simp]
lemma subst_gt_range {M : Lambda} : ∀ {N n}, n > range M → M[n := N] = M := by
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

lemma gt_range_gt_shift {N : Lambda} :
  ∀ {n i j}, n > range N → n + j > range ((↑) i j N) := by
  induction N with
  | var m => intros; simp_all; split_ifs <;> simp <;> omega
  | app N₁ N₂ ih1 ih2 => intros; simp_all
  | abs N ih => intro _ _ _ h; simp [ih h]

@[simp]
lemma shift_unshift_id (M : Lambda) (c i : Nat) : (↓) (c + i) i ((↑) c i M) = M := by
  induction M generalizing c with
  | var n => repeat (first | simp | split_ifs | omega)
  | app M₁ M₂ ih1 ih2 => simp [ih1, ih2]
  | abs M ih =>
    simp; rw [Nat.add_assoc, Nat.add_comm i 1, ← Nat.add_assoc]; exact ih (c + 1)

lemma shift_subst  (M : Lambda) (k j i : Nat) (klej : k ≤ j) (L : Lambda) :
  (↑) k i (M[j := L]) = ((↑) k i M)[j + i := L] := by
  sorry

lemma shift_subst_eq_shift (M N : Lambda) (k i j : Nat) :
  k ≤ i → i < k + (j + 1) → (↑) k j M = ((↑) k (j + 1) M)[i := N] := by sorry

theorem substitution (M N L : Lambda) (n m : Nat) (nlem : n ≤ m) :
  M[n := N][m := L] = M[m + 1 := L][n := N[m - n := L]] := by
  sorry


inductive Shifted : Nat → Nat → Lambda → Prop
  | svar1 {d c n} : n < c → Shifted d c n
  | svar2 {d c n} : c + d ≤ n → d ≤ n → Shifted d c n
  | sapp {d c N₁ N₂} : Shifted d c N₁ → Shifted d c N₂ → Shifted d c (N₁.app N₂)
  | sabs {d c N} : Shifted d (c + 1) N → Shifted d c (λ N)

open Shifted

lemma shift_shifted (d c) (N : Lambda) : Shifted d c ((↑) c d N) := by
  induction N generalizing c <;> simp
  case var n =>
    split_ifs
    . apply svar1; assumption
    . apply svar2 <;> omega
  all_goals constructor <;> aesop

lemma shift_unshift_swap {d c d' c'} {N : Lambda} :
  c' ≤ c → Shifted d' c' N → (↑) c d ((↓) c' d' N) = (↓) c' d' ((↑) (c + d') d N) := by
  intro h₁ h₂
  match N, h₂ with
  | _, sapp _ _ =>
    simp; constructor <;> apply shift_unshift_swap h₁ <;> assumption
  | _, sabs _ =>
    simp
    rw [Nat.add_assoc, Nat.add_comm d' 1, ← Nat.add_assoc]
    apply shift_unshift_swap; omega; assumption
  | var n, svar1 _ =>
    have : n < c := by omega
    have : n < c + d' := by omega
    simp_all
  | var n, svar2 _ _ => repeat (first | split_ifs | omega | simp_all)

lemma weak_shifted {d c} (n) {N : Lambda} : Shifted (d + n) c N → Shifted d (c + n) N := by
  intro h
  match n, h with
  | 0, h => assumption
  | _, svar1 _ => constructor; omega
  | _, svar2 _ _ => apply svar2 <;> omega
  | _, sapp _ _ => apply sapp <;> apply weak_shifted _ <;> assumption
  | n + 1, sabs hN =>
    apply sabs
    rw [Nat.add_right_comm c (n + 1) 1]
    apply weak_shifted _; assumption

lemma shifted_subst' (n : Nat) (N₁ N₂ : Lambda) :Shifted 1 n (N₁ [n := (↑) 0 (n + 1) N₂]) := by
  induction N₁ generalizing n <;> simp
  case var m =>
    split_ifs
    . nth_rw 1 [← Nat.zero_add n]
      nth_rw 2 [Nat.add_comm]
      apply weak_shifted _; apply shift_shifted
    . by_cases h : m < n
      . apply svar1; assumption
      . apply svar2 <;> omega
  case app _ _ ih1 ih2 => apply sapp <;> (first | apply ih1 | apply ih2)
  case abs N ih =>  apply sabs; apply ih

lemma shift_shift_swap {d c d' c'} (N : Lambda) :
  c ≤ c' → (↑) c d ((↑) c' d' N) = (↑) (c' + d) d' ((↑) c d N) := by
  intros h
  induction N generalizing c c' with
  | var => repeat (first | simp | split_ifs | omega)
  | app => simp_all
  | abs =>
    simp_all; nth_rw 2 [Nat.add_assoc]; rw [Nat.add_comm d 1, ← Nat.add_assoc]

@[simp]
lemma shift_subst_swap {d c n} (h : n < c) (N₁ N₂ : Lambda) :
  (↑) c d (N₁ [n := N₂]) = ((↑) c d N₁)[n := (↑) c d N₂] := by
  induction N₁ generalizing N₂ c n with
  | var => repeat (first | simp | split_ifs | omega)
  | app => simp_all
  | abs =>
    simp_all
    have : (↑) 0 1 ((↑) c d N₂) = (↑) (c + 1) d ((↑) 0 1 N₂) := by
      apply shift_shift_swap; omega
    rw [this]

@[simp]
lemma unshift_shift_setoff {d c d' c'} (N : Lambda) :
  c ≤ c' → c' ≤ d' + d + c → (↓) c' d' ((↑) c (d' + d) N) = (↑) c d N := by
  intros h₁ h₂
  induction N generalizing c c' with
  | var => repeat (first | simp | split_ifs | omega)
  | app => simp_all
  | abs _ ih => simp_all; apply ih <;> omega

lemma unshift_subst_swap {c n} (N₁ N₂ : Lambda) : c ≤ n → Shifted 1 c N₁ →
  (↓) c 1 (N₁ [n + 1 := (↑) 0 (c + 1) N₂]) = ((↓) c 1 N₁)[n := (↑) 0 c N₂] := by
  intros h₁ h₂
  sorry
