module BiDirTypeInf.STLC.TypeCheck where

open import Prelude

open import BiDirTypeInf.STLC.Term
open import BiDirTypeInf.Container.List

data TyInf (Γ : Cxt) : Raw → Set where
  ok  : ∀ {τ} → (t : Term Γ inf τ) → TyInf Γ (eraseTerm t)
  bad : ∀ {r} → String → TyInf Γ r

data TyChk (Γ : Cxt) : Raw → Ty → Set where
  ok  : ∀ {τ} → (t : Term Γ chk τ) → TyChk Γ (eraseTerm t) τ
  bad : ∀ {r τ} → String → TyChk Γ r τ

inferTy : ∀ Γ r → TyInf Γ r
checkTy : ∀ Γ r τ → TyChk Γ r τ

inferTy Γ t'@(var x)
  with index∈ Γ x
... | bad n _
  = bad ("when infering " <> show t'
        <> "\nin context " <> show Γ
        <> "\nvar " <> show t' <> " exceeds context by " <> show n)
... | found τ∈Γ
  = ok (var τ∈Γ)
inferTy Γ r@(app s t)
  with inferTy Γ s
... | bad msg
  = bad ("when inferring " <> show r
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
... | ok {bool} s'
  = bad ("when inferring " <> show r
        <> "\nwhen inferring " <> show s
        <> "\nin context " <> show Γ
        <> "\nbool != _->_")
... | ok {σ ⟶ τ} s'
  with checkTy Γ t σ
... | (bad msg)
  = bad ("when inferring " <> show r
        <> "\nin context " <> show Γ
        <> "\n" <> msg )
... | (ok t')
  = ok (app s' t')
inferTy Γ r'@(lam x r)
  = bad ("when inferring " <> show r'
        <> "\nin context " <> show Γ
        <> "\nlam must be checked, not inferred")
inferTy Γ r@(if c t e)
  = bad ("when checking " <> show r
        <> "\nin context " <> show Γ
        <> "\nif must be checked, not inferred")
inferTy Γ tru = ok tru
inferTy Γ fls = ok fls
inferTy Γ t'@(ann τ r)
  with checkTy Γ r τ
... | bad msg
  = bad ("when inferring " <> show t'
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
... | ok t
  = ok (ann τ t)

checkTy Γ r@(var x) τ
  with index∈ Γ x
... | bad n eq
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\nvar " <> show r <> " exceeds context by " <> show n)
... | found {τ'} x∈xs
  with τ == τ'
... | (no neq)
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> show τ' <> " != " <> show τ)
... | (yes refl)
  = ok (chkinf (var x∈xs))
checkTy Γ r@(app s t) τ
  with inferTy Γ (app s t)
... | tyinf-r
  with r
checkTy Γ r@(app s t) τ
  | bad msg | r'
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
checkTy Γ r@(app s t₁) τ
  | ok {τ'} t | .(eraseTerm t)
  with τ == τ'
... | (no neq)
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> show τ' <> " != " <> show τ)
... | (yes refl)
  = ok (chkinf t)
checkTy Γ r'@(lam x r) bool
  = bad ("when checking " <> show r' <> " has type bool"
        <> "\nin context " <> show Γ
        <> "\nlam can never have type bool")
checkTy Γ r'@(lam x r) τ'@(σ ⟶ τ) with checkTy (σ ∷ Γ) r τ
... | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
... | ok t with x == length Γ
... | (no neq)
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "\nin context " <> show Γ
        <> "\nbad var " <> show x <> " in context of size " <> show (length Γ))
... | (yes refl)
  = ok (lam t)
checkTy Γ r@(if c t e) τ with checkTy Γ c bool
... | bad msg
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
... | ok c' with checkTy Γ t τ
... | (bad msg)
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
... | (ok t') with checkTy Γ e τ
... | (bad msg)
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
... | (ok e')
  = ok (if c' t' e')
checkTy Γ tru τ
  with bool == τ
... | no x
  = bad ("when checking tru has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> show τ <> " != bool")
... | yes refl
  = ok (chkinf tru)
checkTy Γ fls τ
  with bool == τ
... | no x
  = bad ("when checking fls has type " <> show τ
        <> "\nin context " <> show Γ
        <> "\n" <> show τ <> " != bool")
... | yes refl
  = ok (chkinf fls)
checkTy Γ r'@(ann τ' r) τ with τ' == τ
... | no neq
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "\nin context " <> show Γ
        <> "\n" <> show τ <> " != " <> show τ')
... | yes refl with checkTy Γ r τ
... | (bad msg)
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "\nin context " <> show Γ
        <> "\n" <> msg)
... | (ok t) = ok (chkinf (ann τ t))

-- private
--   test-if₁ : Raw
--   test-if₁ = lam 0 (if (var 0) fls tru)

--   test-if₂ : Raw
--   test-if₂ = ann (bool ⟶ bool) test-if₁

--   hole : Unit
--   hole = {!!}
