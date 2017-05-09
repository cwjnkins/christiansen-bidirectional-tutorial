module BiDirTypeInf.STLC.Term.Parse where

open import Prelude
import Text.Parse as P

open import BiDirTypeInf.STLC.Term
open import BiDirTypeInf.STLC.Term.Lex

open P Token

pn : P Nat
pn = symbol >>= λ s →
     case s of
       (λ {(tn n) → return n
          ; _     → fail})

p: = token t:
pb = token tb
p⟶ = token t⟶
p$ = token t$
pa = token ta
pt = token tt
pf = token tf
p[ = token t[
p] = token t]
pλ = token tλ
pp = token tp
pi = token ti
ph = token th
pe = token te

paren : ∀ {A} → P A → P A
paren p = p[ *> p <* p]

-- Types
--

{-# TERMINATING #-}
pType pType' : P Ty

pType  = pType' +++ _⟶_ <$> pType' <* p⟶ <*> pType
pType' = bool <$ pb +++ paren pType

parseType : String → Maybe Ty
parseType s = parse! pType (lex s)

private
  test₁-data : String
  test₁-data = "(bool -> bool) -> (bool -> bool) -> bool -> bool"

  test₁ : Ty
  test₁ = fromJust ∘ parseType $ test₁-data

-- Terms
--

pVar : P Raw
pVar = var <$> (p$ *> pn)

apps : Raw → List Raw → Raw
apps f xs = foldl app f xs

pTruFls : P Raw
pTruFls =
  tru <$ pt
  +++ fls <$ pf

{-# NON_TERMINATING #-}
pLam pApp pIf pAnn pLang : P Raw

pLam = lam <$> (pλ *> pn) <*> (pp *> pLang)

pApp = app <$> (pLang <* pa) <*> pLang

pIf = if <$> (pi *> pLang) <*> (ph *> pLang) <*> (pe *> pLang)

pAnn = paren $ flip ann <$> pLang <*> (p: *> pType)

pLang = pVar +++ pIf +++ pTruFls +++ pAnn +++ pLam +++ paren pApp

parseTerm : String → Maybe Raw
parseTerm s = parse! pLang (lex s)

-- private
--   hole : Unit
--   hole = {!!}
--   test₂-data : String
--   test₂-data = "\\ 0 . \\ 1 . \\ 2 . ($0 @ ($1 @ $2))"

--   test₂ : Raw
--   test₂ = fromJust (parseTerm test₂-data)

--   test₃-data : String
--   test₃-data = "\\ 0 . if $0 then fls else tru"

--   test₃ : Raw
--   test₃ = fromJust (parseTerm test₃-data)
