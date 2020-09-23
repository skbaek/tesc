{-# OPTIONS --prop #-} 

module attv where

open import Data.Unit.Base renaming (⊤ to Unit)
open import Data.Maybe.Base 
  renaming (map to map?)
  renaming (_>>=_ to _?>=_)
import IO.Primitive as Prim
open import IO
  renaming (_>>=_ to _>>>=_)
  renaming (_>>_ to _>>>_)
open import basic 

main : Prim.IO (Maybe Unit) 
main = run read-check