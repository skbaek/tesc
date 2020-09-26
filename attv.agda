module attv where

open import Data.Unit.Base renaming (⊤ to Unit)
open import Agda.Builtin.Nat
open import Data.Integer
open import Agda.Builtin.String
open import Data.List -- renaming (or to disj) renaming(and to conj)
open import Data.Maybe.Base 
  renaming (map to map?)
  renaming (_>>=_ to _?>=_)
open import Agda.Builtin.Coinduction
import IO.Primitive as Prim
open import IO
  renaming (_>>=_ to _>>>=_)
  renaming (_>>_ to _>>>_)
open import basic 
  renaming (_>>_ to _?>_)

{-# FOREIGN GHC import qualified System.Exit #-}

postulate prim-exit-failure : Prim.IO Unit

{-# COMPILE GHC prim-exit-failure = System.Exit.exitFailure #-}

exit-failure : IO Unit 
exit-failure = lift prim-exit-failure

_>>=_ : {A : Set} {B : Set} → IO A → (A → IO B) → IO B
_>>=_ f g = ♯ f >>>= \ x → ♯ (g x)

_>>_  : {A : Set} {B : Set} →  IO A → IO B → IO B
_>>_ f g = ♯ f >>> ♯ g 

read-check : IO Unit 
read-check = do 
  (pn ∷ x) ← get-args
    where [] → (put-str-ln "No proof file name provided." >> exit-failure)
  -- put-str "Using proof file = " 
  -- put-str pn 
  ps ← getContents
  (just P) ← return (read-prob ps empty-prob)
    where nothing → (put-str-ln "Failed to load problem." >> exit-failure)
  cs ← readFiniteFile pn
  -- put-str "Using proof = "
  -- put-str cs
  (just tt) ← return (check (primStringToList cs) ⟨ P , ⟨ [] , 0 ⟩ ∷ [] , [] , [] ⟩)
    where nothing → (put-str-ln "Invalid proof." >> exit-failure)
  put-str-ln "ATTV : Proof verified."

main : Prim.IO Unit 
main = run read-check