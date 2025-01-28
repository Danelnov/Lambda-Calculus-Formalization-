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

def Lambda.shift (c : Nat) (i : Int) : Lambda → Lambda
  | var n =>
    if n < c then var n
    else var (n + i).toNat
  | app e₁ e₂ => app (e₁.shift c i) (e₂.shift c i)
  | abs e => abs (e.shift (c + 1) i)

def Lambda.subst (v : Lambda) (e : Lambda) (m : Nat) : Lambda :=
  match v with
  | var n => if n = m then e else var n
  | app v₁ v₂ => app (v₁.subst e m) (v₂.subst e m)
  | abs v₁ => abs $ v₁.subst (e.shift 0 1) (m + 1)

def Redex (e : Lambda) := ∃ (e₁ e₂ : Lambda), e = (λ e₁).app e₂

def Lambda.beta : Lambda → Lambda
  | app e₁ e₂ =>
    match e₁ with
    | abs v => (v.subst (e₂.shift 0 1) 0).shift 0 (-1)
    | _ => app e₁ e₂
  | e => e

inductive BetaR : Lambda → Lambda → Prop
| basis (M : Lambda) : BetaR M M.beta
| app_left (M N L) : BetaR M N → BetaR (.app M L) (.app N L)
| app_right (M N L) : BetaR M N → BetaR (.app L M) (.app L N)
| abs (M N) : BetaR M N → BetaR (λ M) (λ N)
| refl (M) : BetaR M M

inductive BetaRR : Lambda → Lambda → Prop
| beta (M N) : BetaR M N → BetaRR M N
| trans (M N L) : BetaRR M N → BetaRR N L → BetaRR M L
