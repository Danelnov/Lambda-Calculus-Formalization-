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

instance : Coe Nat Lambda := ⟨λ n => Lambda.var n⟩

instance : OfNat Lambda n := ⟨Lambda.var n⟩

def Lambda.shift (c i : Nat) : Lambda → Lambda
  | var n =>
    if n < c then var n
    else var (n + i)
  | app e₁ e₂ => app (e₁.shift c i) (e₂.shift c i)
  | abs e => abs $ e.shift (c + 1) i

def Lambda.unshift (c i : Nat) : Lambda → Lambda
  | var n =>
    if n < c then var n
    else var (n - i)
  | app e₁ e₂ => app (e₁.unshift c i) (e₂.unshift c i)
  | abs e => abs $ e.unshift (c + 1) i

notation:60 "↑"  c:61  i:62  t:63 => Lambda.shift c i t
notation:60 "↓"  c:61  i:62  t:63 => Lambda.unshift c i t

def Lambda.subst (v : Lambda) (n : Nat) (e : Lambda) :=
  match v with
  | var m =>
    if m = n then e
    else var m
  | app v₁ v₂ => app (v₁.subst n e) (v₂.subst n e)
  | abs v₁ => abs $ v₁.subst (n + 1) (e.shift 0 1)

notation:65 t:65 "[" k " ↦ " s:65 "]" => Lambda.subst t k s

inductive Beta : Lambda → Lambda → Prop
  | basis (M N : Lambda) : Beta ((λ M).app N) ((M.subst 0 (N.shift 0 1)).unshift 0 1)
  | appr (M N L : Lambda) : Beta N M → Beta (N.app L) (M.app L)
  | appl (M N L : Lambda): Beta N M → Beta (L.app N) (L.app M)
  | abs (N M) : Beta N M → Beta (λ N) (λ M)

infixl:65 " →β " => Beta

inductive BetaTR : Lambda → Lambda → Prop
  | refl (M) : BetaTR M M
  | beta (M N) : Beta M N → BetaTR M N
  | trans (M N L) : BetaTR M N → BetaTR N L → BetaTR M L

infixl:65 " ⇒β " => BetaTR
