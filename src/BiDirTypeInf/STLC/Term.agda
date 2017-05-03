module BiDirTypeInf.STLC.Term where

open import Prelude
open import Container.List

infixr 0 _⟶_
data Ty : Set where
  bool : Ty
  _⟶_  : (σ τ : Ty) → Ty

private
  showTy : Ty → String
  showTy bool
    = "bool"
  showTy (σ ⟶ τ)
    = "(" <> showTy σ <> " -> " <> showTy τ <> ")"

  eqTy : (τ σ : Ty) → Dec (τ ≡ σ)
  eqTy bool bool = yes refl
  eqTy bool (σ ⟶ σ₁) = no (λ ())
  eqTy (τ ⟶ τ₁) bool = no (λ ())
  eqTy (τ ⟶ τ₁) (σ ⟶ σ₁)
    with eqTy τ σ
  ... | no  ne
    = no (λ { refl → ne refl})
  ... | yes refl
    with eqTy τ₁ σ₁
  ... | (no ne)
    = no (λ { refl → ne refl})
  ... | (yes refl)
    = yes refl

data Raw : Set where
  var : Nat → Raw
  app : (s t : Raw) → Raw
  lam : Nat → Raw → Raw
  if  : (c t e : Raw) → Raw
  tru fls : Raw
  ann : Ty → Raw → Raw

private
  showRaw : Raw → String
  showRaw (var x)
    = "$" <> show x
  showRaw (app s t)
    = "(" <> showRaw s <> " @ " <> showRaw t <> ")"
  showRaw (lam x r)
    = "(\\" <> show x <> " . " <> showRaw r <> ")"
  showRaw (if c t e)
    = "(if " <> showRaw c <> " then " <> showRaw t <> " else " <> showRaw e <> ")"
  showRaw tru
    = "tru"
  showRaw fls
    = "fls"
  showRaw (ann τ r)
    = "(" <> showRaw r <> " : " <> showTy τ <> ")"

instance
  ShowTy : Show Ty
  ShowTy = simpleShowInstance showTy

  EqTy : Eq Ty
  EqTy = record { _==_ = eqTy }

  ShowRaw : Show Raw
  ShowRaw = simpleShowInstance showRaw

data TCMode : Set where
  chk inf : TCMode

Cxt = List Ty

data Term (Γ : Cxt) : TCMode → Ty → Set where
  var : ∀ {τ}
        → τ ∈ Γ
        --------------
        → Term Γ inf τ
  app : ∀ {σ τ}
        → Term Γ inf (σ ⟶ τ) → Term Γ chk σ
        -----------------------------------
        → Term Γ inf τ
  lam : ∀ {σ τ}
        → Term (σ ∷ Γ) chk τ
        --------------------
        → Term Γ chk (σ ⟶ τ)
  if  : ∀ {τ}
        → Term Γ chk bool → Term Γ chk τ → Term Γ chk τ
        -----------------------------------------------
        → Term Γ chk τ
  tru fls :
        --------------
        Term Γ inf bool
  ann : ∀ τ
        → Term Γ chk τ
        --------------
        → Term Γ inf τ
  chkinf : ∀ {τ}
        → Term Γ inf τ
        --------------
        → Term Γ chk τ

eraseTerm : ∀ {Γ m τ} → Term Γ m τ → Raw
eraseTerm (var x)
  = var (forgetAny x)
eraseTerm (app s t)
  = app (eraseTerm s) (eraseTerm t)
eraseTerm {Γ} (lam t)
  = lam (length Γ ) (eraseTerm t)
eraseTerm (if c t e)
  = if (eraseTerm c) (eraseTerm t) (eraseTerm e)
eraseTerm tru
  = tru
eraseTerm fls
  = fls
eraseTerm (ann τ t)
  = ann τ (eraseTerm t)
eraseTerm (chkinf t)
  = eraseTerm t

data TyInf (Γ : Cxt) : Raw → Set where
  ok  : ∀ {τ} → (t : Term Γ inf τ) → TyInf Γ (eraseTerm t)
  bad : ∀ {r} → String → TyInf Γ r

data TyChk (Γ : Cxt) : Raw → Ty → Set where
  ok  : ∀ {τ} → (t : Term Γ chk τ) → TyChk Γ (eraseTerm t) τ
  bad : ∀ {r τ} → String → TyChk Γ r τ

inferTy : ∀ Γ r → TyInf Γ r
checkTy : ∀ Γ r τ → TyChk Γ r τ

-- TODO index w/ proof
inferTy Γ (var x) = {!!}
inferTy Γ (app s t) = {!!}
inferTy Γ (lam x r) = {!!}
inferTy Γ (if c t e) = {!!}
inferTy Γ tru = ok tru
inferTy Γ fls = ok fls
inferTy Γ t'@(ann τ r)
  with checkTy Γ r τ
... | bad msg
  = bad ("when checking " <> show t' <> " has type " <> show τ <> "\n" <> msg)
... | ok t
  = ok (ann τ t)

checkTy Γ (var x) τ = {!!}
checkTy Γ (app r r₁) τ = {!!}
checkTy Γ (lam x r) τ = {!!}
checkTy Γ (if r r₁ r₂) τ = {!!}
checkTy Γ tru τ
  with eqTy bool τ
... | no x
  = bad (show τ <> " != bool\nwhen checking tru has type " <> show τ )
... | yes refl
  = ok (chkinf tru)
checkTy Γ fls τ
  with eqTy bool τ
... | no x
  = bad (show τ <> " != bool\nwhen checking fls has type " <> show τ )
... | yes refl
  = ok (chkinf fls)
checkTy Γ (ann x r) τ = {!!}
