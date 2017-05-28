module BiDirTypeInf.RecTy.TypeCheck where

open import Prelude
open import Container.List

open import BiDirTypeInf.Container.List
open import BiDirTypeInf.RecTy.Ty
open import BiDirTypeInf.RecTy.Term

data TyInf (Γ : Cxt) : Raw → Set where
  ok  : ∀ {τ} (t : Term Γ inf τ) → TyInf Γ (eraseTerm t)
  bad : ∀ {r} (msg : String)     → TyInf Γ r

data TyChk (Γ : Cxt) : Raw → Ty → Set where
  ok  : ∀ {τ} (t : Term Γ chk τ) → TyChk Γ (eraseTerm t) τ
  bad : ∀ {r τ} (msg : String)   → TyChk Γ r τ

inferTy : ∀ Γ r → TyInf Γ r
checkTy : ∀ Γ r τ → TyChk Γ r τ

inferTy Γ r@(var x) with index∈ Γ x
... | bad n x₁
  = bad ("when inferring " <> show r
        <> "\\n in context " <> show Γ
        <> "\\n" <> show r <> " exceeds cxt by " <> show n)
... | found x∈Γ
  = ok (var x∈Γ)
inferTy Γ r'@(app o r) with inferTy Γ o
... | bad msg
  = bad ("when inferring " <> show r'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok {σ ⟶ τ} s with checkTy Γ r σ
... | (bad msg)
  = bad ("when inferring " <> show r'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | (ok t)
  = ok (app s t)
inferTy Γ r'@(app .(eraseTerm s) r)
    | ok {τ} s
  = bad ("when checking " <> show r'
        <> "\\n " <> show τ <> " != _ -> _")
inferTy Γ r'@(lam x r)
  = bad ("when inferring " <> show r'
        <> "\\n lam must be checked, not inferred")
inferTy Γ r@(if c t e)
  = bad ("when inferring " <> show r
        <> "\\n if must be checked, not inferred")
inferTy Γ tru = ok tru
inferTy Γ fls = ok fls
inferTy Γ r'@(in₁ r)
  = bad ("when inferring " <> show r'
        <> "\\n in1 must be checked, not inferred")
inferTy Γ r'@(in₂ r)
  = bad ("when inferring " <> show r'
        <> "\\n in2 must be checked, not inferred")
inferTy Γ r'@(pr o r) with inferTy Γ o | inferTy Γ r
... | bad msg | _
  = bad ("when inferring " <> show r'
        <> "\\n when inferring pr1 " <> show o
        <> "\\n" <> msg)
... | ok s | (bad msg)
  = bad ("when inferring " <> show r'
        <> "\\n when inferring pr2 " <> show r
        <> "\\n" <> msg)
... | ok s | (ok t)
  = ok (pr s t)
inferTy Γ r'@(pr₁ r) with inferTy Γ r
... | bad msg
  = bad ("when inferring " <> show r'
        <> "\\n" <> msg)
... | ok {prod σ τ} t
  = ok (pr₁ t)
... | ok {τ} t
  = bad ("when inferring " <> show r'
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ <> " != prod _ _")
inferTy Γ r'@(pr₂ r) with inferTy Γ r
... | bad msg
  = bad ("when inferring " <> show r'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok {prod σ τ} t
  = ok (pr₂ t)
... | ok {τ} t
  = bad ("when inferring " <> show r'
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ <> " != prod _ _")
inferTy Γ c'@(case c l r)
  = bad ("when inferring " <> show c'
        <> "\\n in context " <> show Γ
        <> "case must be checked, not inferred")
inferTy Γ r'@(unrll r) with inferTy Γ r
... | bad msg
  = bad ("when inferring " <> show r'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok {μ τ} t
  rewrite iso-rec τ = ok (unrll {τ = unroll (μ τ)} t)
... | ok {τ} t
  = bad ("when checking " <> show r'
        <>"\\n" <> show τ <> " is not a recty")
inferTy Γ r'@(rll r)
  = bad ("when inferring " <> show r'
        <> "\\n rll must be checked, not inferred")
inferTy Γ r'@(ann τ r) with checkTy Γ r τ
... | bad msg
  = bad ("when inferring " <> show r'
        <> "\\n" <> msg)
... | ok t = ok (ann τ t)


checkTy Γ r@(var x) τ with index∈ Γ x
... | bad n x₁
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show r <> " exceeds cxt by " <> show n)
... | found {τ'} x∈xs with τ' == τ
... | (no neq)
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ' <> " != " <> show τ)
... | (yes refl)
  = ok (chkinf (var x∈xs))

checkTy Γ r'@(app o r) τ  with inferTy Γ r'
... | r'-inf              with r' | inspect r'
checkTy Γ (app o r) τ
  | bad msg
  | r″ | insp
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
checkTy Γ (app o r) τ
    | ok {τ'} t
    | .(eraseTerm t) | insp with τ' == τ
... | (no neq)
  = bad ("when checking " <> show r <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ' <> " != " <> show τ)
... | (yes refl)
  = ok (chkinf t)

checkTy Γ r'@(lam x r) τ'@(σ ⟶ τ) with checkTy (σ ∷ Γ) r τ
... | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "\\n in context <> " <> show Γ
        <> "\\n" <> msg)
... | ok t with x == length Γ
... | (no neq)
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "\\n in context <> " <> show Γ
        <> "\\nbad var $" <> show x <> " in context of size " <> show (length Γ))
... | (yes refl)
  = ok (lam t)
checkTy Γ r'@(lam x r) τ
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context <> " <> show Γ
        <> "\\n" <> show τ <> " != _->_")

checkTy Γ r'@(if c t e) τ with checkTy Γ c bool | checkTy Γ t τ | checkTy Γ e τ
...  | bad msg | _ | _
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n when checking " <> show c <> " has type bool"
        <> "\\n in context <> " <> show Γ
        <> "\\n" <> msg)
...  | ok c' | (bad msg) | _
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n when checking " <> show t <> " has type" <> show τ
        <> "\\n in context <> " <> show Γ
        <> "\\n" <> msg)
...  | ok c' | (ok t') | (bad msg)
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n when checking " <> show e <> " has type" <> show τ
        <> "\\n in context <> " <> show Γ
        <> "\\n" <> msg)
...  | ok c' | (ok t') | (ok e')
  = ok (if c' t' e')

checkTy Γ tru bool = ok (chkinf tru)
checkTy Γ tru τ
  = bad ("when checking tru has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ <> " != bool")
checkTy Γ fls bool = ok (chkinf fls)
checkTy Γ fls τ
  = bad ("when checking fls has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ <> " != bool")

checkTy Γ r'@(in₁ r) τ'@(eith σ τ) with checkTy Γ r σ
... | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show  τ'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok t
  = ok (in₁ t)
checkTy Γ r'@(in₁ r) τ
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context Γ"
        <> "\\n" <> show τ <> " != eith _ _")

checkTy Γ r'@(in₂ r) τ'@(eith σ τ) with checkTy Γ r τ
... | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show  τ'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok t
  = ok (in₂ t)
checkTy Γ r'@(in₂ r) τ
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context Γ"
        <> "\\n" <> show τ <> " != eith _ _")

checkTy Γ r'@(pr o r) τ'@(prod σ τ) with checkTy Γ o σ | checkTy Γ r τ
... | bad msg | _
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "when checking " <> show o
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok s | (bad msg)
  = bad ("when checking " <> show r' <> " has type " <> show τ'
        <> "when checking " <> show r
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok s | ok t
  = ok (pr s t)
checkTy Γ r'@(pr o r) τ
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ <> " != prod _ _")

checkTy Γ r'@(pr₁ r) τ with inferTy Γ r
... | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> msg)
checkTy Γ r'@(pr₁ .(eraseTerm t)) τ | ok {τ″@(prod σ' τ')} t with σ' == τ
... | (no neq)
  = bad ("when checking " <> show r' <> " has type " <> show τ″
        <> "\\n in context " <> show Γ
        <> "\\n" <> show σ' <> " != " <> show τ)
... | (yes refl)
  = ok (chkinf (pr₁ t))
checkTy Γ r'@(pr₁ .(eraseTerm t)) τ₂ | ok {τ} t
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ <> " != prod _ _" )

checkTy Γ r'@(pr₂ r) τ with inferTy Γ r
... | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> msg)
checkTy Γ r'@(pr₂ .(eraseTerm t)) τ | ok {τ″@(prod σ' τ')} t with τ' == τ
... | (no neq)
  = bad ("when checking " <> show r' <> " has type " <> show τ″
        <> "\\n in context " <> show Γ
        <> "\\n" <> show σ' <> " != " <> show τ)
... | (yes refl)
  = ok (chkinf (pr₂ t))
checkTy Γ r'@(pr₂ .(eraseTerm t)) τ₂ | ok {τ} t
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ <> " != prod _ _" )

checkTy Γ (case c l r) τ with inferTy Γ c
checkTy Γ r″@(case c l r) τ | bad msg
  = bad ("when checking " <> show r″ <> " has type " <> show τ
        <> "\\n in context Γ"
        <> "\\n" <> msg)
checkTy Γ r″@(case .(eraseTerm c') l r) τ | ok {eith σ' τ'} c'
  with checkTy Γ l (σ' ⟶ τ) | checkTy Γ r (τ' ⟶ τ)
... | (bad msg) | _
  = bad ("when checking " <> show r″ <> " has type " <> show τ
        <> "\\n when checking " <> show l <> " has type " <> show σ'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | (ok l') | (bad msg)
  = bad ("when checking " <> show r″ <> " has type " <> show τ
        <> "\\n when checking " <> show r <> " has type " <> show τ'
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | (ok l') | (ok r')
  = ok (case c' l' r')
checkTy Γ r″@(case .(eraseTerm t) l r) τ | ok {τ'} t
  = bad ("when checking " <> show r″ <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ' <> " != eith _ _")

checkTy Γ r'@(unrll r) τ with inferTy Γ r
... | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> msg)
... | ok {τ = τ'} t with τ' == roll τ
... | (no x)
  = bad (("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ' <> " != " <> show (roll τ)))
checkTy Γ (unrll .(eraseTerm t)) τ | ok {.(roll τ)} t | (yes refl)
  = ok (chkinf (unrll t))

checkTy Γ (rll r) τ with checkTy Γ r (unroll τ)
checkTy Γ r'@(rll r) τ | bad msg
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show msg)
checkTy Γ (rll .(eraseTerm t)) τ | ok t
  = ok (rll t)

checkTy Γ r'@(ann τ' r) τ with τ' == τ
... | no neq
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> "\\n" <> show τ' <> " != " <> show τ')
... | yes refl with checkTy Γ r τ
... | (bad msg)
  = bad ("when checking " <> show r' <> " has type " <> show τ
        <> "\\n in context " <> show Γ
        <> msg)
... | (ok t)
  = ok (chkinf (ann τ t))

private
  list : Ty
  list = μ (eith bool (prod bool (tv 0)))

  module Test₁ where
    raw-ok : Raw
    raw-ok = ann list (rll (in₁ tru))

    raw-bad : Raw
    raw-bad = ann list (rll (in₂ tru))

    term-chk-ok : TyChk [] raw-ok list
    term-chk-ok = checkTy [] raw-ok list

    term-chk-bad : TyChk [] raw-bad list
    term-chk-bad = checkTy [] raw-bad list

    -- hole : Unit
    -- hole = {!!}

  module Test₂ where
    raw-ok : Raw
    raw-ok
      = ann (list ⟶ bool)
            (lam 0
                 (case (unrll (var 0))
                       (lam 1 (var 0))
                       (lam 1 (pr₁ (var 0)))))

    raw-bad : Raw
    raw-bad
      = ann (list ⟶ bool)
            (case (var 0)
                  (lam 1 (var 0))
                  (lam 1 (pr₁ (var 0))))

    -- stuck on postulate iso-rec
    test-inf-ok : TyInf [] raw-ok
    test-inf-ok = inferTy [] raw-ok

    -- hole : Unit
    -- hole = {!!}
