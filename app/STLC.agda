module STLC where

open import Prelude

open import BiDirTypeInf.STLC.Term
open import BiDirTypeInf.STLC.Term.Parse
open import BiDirTypeInf.STLC.Term.Lex

open import BiDirTypeInf.STLC.TypeCheck

usage : IO Unit
usage = getProgName >>= λ n → putStrLn $ n <> " <text> "

main : IO Unit
main
  = getArgs
    >>= (λ { (text ∷ []) → putStrLn ∘ prog $ text
           ; ("parse" ∷ text ∷ []) → putStrLn ∘ progParse $ text
           ; _ → usage >> exitWith (Failure 1)})
  where
  prog : String → String
  prog text with parseTerm text
  ... | nothing = "failed to parse!"
  ... | just r with inferTy [] r
  ... | (bad msg) = msg
  ... | (ok {τ} _) = show r <> "\nhas type: " <> show τ

  progParse : String → String
  progParse text = show (parseTerm' text)
