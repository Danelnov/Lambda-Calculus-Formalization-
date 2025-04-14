inductive Lambda
  | var : Nat → Lambda
  | abs : Lambda → Lambda
  | app : Lambda → Lambda → Lambda

prefix:100 "λ " => Lambda.abs

def Lambda.toString : Lambda → String
  | var n => Nat.toDigits 10 n |> List.asString
  | abs e => s!"λ {e.toString}"
  | app e₁ e₂ =>
    match e₁, e₂ with
    | abs _, _ => s!"(({e₁.toString}) {e₂.toString})"
    | _, _ => s!"({e₁.toString} {e₂.toString})"

instance : ToString Lambda := ⟨Lambda.toString⟩

instance : Repr Lambda where
  reprPrec M _ := M.toString.toFormat

def Lambda.shift (c : Nat) (i : Nat) : Lambda → Lambda
  | var n =>
    if n < c then var n
    else var (n + i)
  | app e₁ e₂ => app (e₁.shift c i) (e₂.shift c i)
  | abs e => abs (e.shift (c + 1) i)


notation:60 "↑"  c:61  i:62  t:63 => Lambda.shift c i t

def Lambda.subst (v : Lambda) (e : Lambda) (m : Nat) : Lambda :=
  match v with
  | var n =>
    if n < m then var n
    else if n = m then e.shift 0 m
    else var (n - 1)
  | app v₁ v₂ => app (v₁.subst e m) (v₂.subst e m)
  | abs v₁ => abs $ v₁.subst e (m + 1)

notation:65 t:65 "[" k " ↦ " s:65 "]" => Lambda.subst t s k

def Redex (e : Lambda) := ∃ (e₁ e₂ : Lambda), e = (λ e₁).app e₂

-- def Lambda.beta : Lambda → Lambda
--   | app e₁ e₂ =>
--     match e₁ with
--     | abs v => (v.subst (e₂.shift 0 1) 0).shift 0 (-1)
--     | _ => app e₁ e₂
--   | e => e

-- inductive BetaR : Lambda → Lambda → Prop
--   | basis (M : Lambda) : BetaR M M.beta
--   | app_left (M N L) : BetaR M N → BetaR (.app M L) (.app N L)
--   | app_right (M N L) : BetaR M N → BetaR (.app L M) (.app L N)
--   | abs (M N) : BetaR M N → BetaR (λ M) (λ N)
--   | refl (M) : BetaR M M

-- inductive BetaRR : Lambda → Lambda → Prop
--   | beta (M N) : BetaR M N → BetaRR M N
--   | trans (M N L) : BetaRR M N → BetaRR N L → BetaRR M L


theorem sustitution_lem1 (n m : Nat) (N : Lambda)
  : ∀ (i j : Nat), i ≤ j → j ≤ i + m → (N.shift i m).shift j n = N.shift i (m + n)
  := by
  induction N with
  | var k =>
    intro i j ilej jlem1
    simp_all [Lambda.shift]
    rcases Nat.lt_trichotomy k i with klei | rfl | kgti
    . simp [klei]
      rw [Lambda.shift]
      simp [Nat.lt_of_lt_of_le klei ilej]
    . simp
      rw [Lambda.shift]
      simp [Nat.not_lt.mpr jlem1]
      rw [Nat.add_assoc]
    . simp [Nat.not_lt_of_gt kgti]
      rw [Lambda.shift]
      have : i + m < k + m := by exact Nat.add_lt_add_right kgti m
      have : j < k + m := by exact Nat.lt_of_le_of_lt jlem1 this
      simp [Nat.not_lt_of_gt this]
      rw [Nat.add_assoc]
  | app e v ihe ihv =>
    intro i j ilej jlemi
    simp_all [Lambda.shift]
  | abs e ih =>
    intro i j ilej jleim
    simp_all [Lambda.shift]
    apply ih
    exact Nat.add_le_add_right ilej 1
    rw [Nat.add_assoc, Nat.add_comm 1 m, ← Nat.add_assoc]
    exact Nat.add_le_add_right jleim 1

theorem sustitution_lem2 (i : Nat) (N L : Lambda)
  : ∀ (k j : Nat), k ≤ j → (N[j ↦ L]).shift k i = (N.shift k i)[j + i ↦ L] := by
  induction N with
  | var n =>
    intro k j klej
    rcases Nat.lt_trichotomy n k with nlek | rfl | ngtk
    . have nlej : n < j := Nat.lt_of_lt_of_le nlek klej
      have nleji : n < j + i := Nat.lt_add_right i nlej
      simp [Lambda.shift, Lambda.subst, nlek, nleji, nlej]
    . rcases Or.symm (Nat.eq_or_lt_of_le klej) with nlej | rfl
      . simp [Lambda.subst, Lambda.shift, nlej]
      . simp_all [Lambda.subst, Lambda.shift]
        apply sustitution_lem1 <;> simp
    . rcases Nat.lt_trichotomy n j with nlej | rfl | ngtj
      . simp [Lambda.subst, Lambda.shift, Nat.not_lt_of_gt ngtk, nlej]
      . simp [Lambda.subst, Lambda.shift, Nat.not_lt_of_gt ngtk]
        apply sustitution_lem1 <;> simp [klej]
      .
        have : ¬ (n - 1 < k) := by
          intro h
          apply Nat.lt_irrefl (n - 1)
          apply Nat.lt_of_lt_of_le h
          exact Nat.le_sub_one_of_lt ngtk
        simp [
          Lambda.subst,
          Lambda.shift,
          Nat.not_lt_of_gt ngtj,
          Ne.symm (Nat.ne_of_lt ngtj),
          this,
          Nat.not_lt_of_gt ngtk
        ]
        rw [Nat.sub_add_comm]
        exact (Nat.zero_lt_of_lt ngtk)
  | app e v ihe ihv =>
    intro i j ilej
    simp_all [Lambda.shift, Lambda.subst]
  | abs e ihe =>
    intro k j ilej
    simp_all [Lambda.subst, Lambda.shift]
    rw [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc]

theorem sustitution (n m : Nat) (nlem : n ≤ m) (M N L : Lambda)
  : M[n ↦ N][m ↦ L] = M[m + 1 ↦ L][n ↦ N[m - n ↦ L]] := by
  induction M with
  | var k =>
    rcases Nat.lt_trichotomy k n with klen | rfl | kgtn
    -- Case k < n
    . rw [Lambda.subst, Lambda.subst]
      have klem1 : k < m + 1 := by
        apply Nat.lt_of_lt_of_le
        exact klen
        exact Nat.le_add_right_of_le nlem
      have klem : k < m := by exact Nat.lt_of_lt_of_le klen nlem
      simp [klen, klem1]
      rw [Lambda.subst, Lambda.subst]
      simp [klem, klen]
    -- Case k = n
    . rw [Lambda.subst]
      simp
      have klem1 : k < m + 1 := by exact Nat.lt_add_one_of_le nlem
      rw [Lambda.subst]
      simp [klem1]
      rw [Lambda.subst]
      simp
      have zero_le_mmk : 0 ≤ m - k := (Nat.le_sub_iff_add_le' nlem).mpr nlem
      rw [eq_comm]
      have := by
        apply sustitution_lem2 k N L
        exact zero_le_mmk
      simp [Nat.sub_add_cancel nlem] at this
      assumption
    -- case n < k
    .
      have (h₁ : 0 < k) : k - 1 < m ↔ k < m + 1 := by
        conv =>
          lhs
          rw [← Nat.add_lt_add_iff_right, Nat.sub_add_cancel h₁]
          simp
      simp [
        Lambda.subst,
        Nat.not_lt_of_gt kgtn,
        Ne.symm (Nat.ne_of_lt kgtn)
      ]
      simp [this <| Nat.zero_lt_of_lt kgtn]
      rcases Nat.lt_trichotomy k (m + 1) with kltm1 | rfl | kgtm1
      . simp [
          kltm1,
          Lambda.subst,
          Nat.not_lt_of_gt kgtn,
          Ne.symm (Nat.ne_of_lt kgtn)
        ]
      . sorry
      .




#check sustitution_lem2
