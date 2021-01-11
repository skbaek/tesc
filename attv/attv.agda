module attv where

open import Function.Base
open import Data.Unit.Base 
open import Agda.Builtin.Nat
open import Data.Integer
open import Data.Product
open import Agda.Builtin.String
open import Data.List  
open import Data.Bool
open import Data.Maybe.Base 
  using (just)
  using (nothing)
open import Agda.Builtin.Coinduction
import IO.Primitive as Prim
open import IO
  renaming (_>>=_ to _>>>=_)
  renaming (_>>_ to _>>>_)
open import verify 
  using (parse-verify)
  -- using (cont)
  -- using (stop)
open import Codata.Musical.Colist 
  renaming (length to length*) 
  renaming (map to map*) 
  renaming ([_] to [_]*) 
  renaming (_∷_ to _∷*_) 
  renaming (_++_ to _++*_) 
open import Codata.Musical.Costring 
open import Data.Bool using (if_then_else_)
open import basic using (Chars)

postulate 
  prim-get-args : Prim.IO (List String)
  prim-exit-failure : Prim.IO ⊤

{-# FOREIGN GHC import qualified System.Environment as Env #-}
{-# FOREIGN GHC import Data.Text #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# COMPILE GHC prim-get-args = fmap (fmap pack) Env.getArgs #-}
{-# COMPILE GHC prim-exit-failure = System.Exit.exitFailure #-}

exit-failure : IO ⊤ 
exit-failure = lift prim-exit-failure

_>>=_ : {A : Set} {B : Set} → IO A → (A → IO B) → IO B
_>>=_ f g = ♯ f >>>= \ x → ♯ (g x)

_>>_  : {A : Set} {B : Set} →  IO A → IO B → IO B
_>>_ f g = ♯ f >>> ♯ g 

skip : IO ⊤ 
skip = lift (Prim.return tt)

get-args : IO (List String)
get-args = lift prim-get-args

put-str-ln : String → IO ⊤
put-str-ln s = putStr s >> (putStr "\n" >> skip) 

costring-to-chars : Costring → Chars 
costring-to-chars (c ∷* cs) = c ∷ costring-to-chars (♭ cs)
costring-to-chars _ = []

-- print-result : Res ⊤ → IO ⊤ 
-- print-result (cont tt x) = put-str-ln "Proof verified (kernel = ATTV)."
-- print-result (stop s) = do 
--   putStr "Invalid proof : " 
--   put-str-ln s
--   exit-failure

print-result : Bool → IO ⊤ 
print-result true = put-str-ln "Proof verified (kernel = ATTV)."
print-result false = do 
  putStr "Invalid proof" 
  exit-failure

io-verify : IO ⊤ 
io-verify = do 
  (pn ∷ _) ← get-args
    where _ → (put-str-ln "Missing proof file name." >> exit-failure)
  ps ← getContents
  cs ← readFiniteFile pn >>= (return ∘ primStringToList)
  print-result (parse-verify (costring-to-chars ps) cs) 

-- io-verify : IO ⊤ 
-- io-verify = do 
--   (pn ∷ (md ∷ x)) ← get-args
--     where _ → (put-str-ln "Missing proof file name or mode." >> exit-failure)
--   ps ← getContents
--   cs ← readFiniteFile pn >>= (return ∘ primStringToList)
--   print-result (check (primStringEquality md "lazy") (costring-to-chars ps) cs) 

main : Prim.IO ⊤ 
main = run io-verify