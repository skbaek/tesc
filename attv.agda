module attv where

open import Function.Base
open import Data.Unit.Base 
open import Agda.Builtin.Nat
open import Data.Integer
open import Data.Product
open import Agda.Builtin.String
open import Data.List 
open import Data.Maybe.Base 
  renaming (map to map?)
  renaming (_>>=_ to _?>=_)
open import Agda.Builtin.Coinduction
import IO.Primitive as Prim
open import IO
  renaming (_>>=_ to _>>>=_)
  renaming (_>>_ to _>>>_)
open import basic 
open import verify 
  using (read-prob) 
  using (verify)
open import Codata.Musical.Costring using (Costring)
open import Codata.Musical.Colist 
  renaming (_∷_ to _∷*_)
  renaming (length to length*)

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

nop : IO ⊤ 
nop = lift (Prim.return tt)

get-args : IO (List String)
get-args = lift prim-get-args

put-str-ln : String → IO ⊤
put-str-ln s = putStr s >> (putStr "\n" >> nop) 

costring-to-chars : Costring → Chars
costring-to-chars (c ∷* cs) = c ∷ (costring-to-chars (♭ cs))
costring-to-chars _ = []

io-verify = do 
  (pn ∷ x) ← get-args
    where [] → (put-str-ln "No proof file name provided." >> exit-failure)
  ps ← getContents
  cs0 ← return (costring-to-chars ps)
  (just (P , _)) ← return (read-prob (length cs0) cs0)
    where nothing → (put-str-ln "Failed to load problem." >> exit-failure)
  cs ← readFiniteFile pn >>= (return ∘ primStringToList)
  (just (tt , _)) ← return (verify P [] (length cs) cs) 
    where nothing → (put-str-ln "Invalid proof." >> exit-failure)
  put-str-ln "ATTV : Proof verified."

main : Prim.IO ⊤ 
main = run io-verify