open import Agda.Builtin.Coinduction
open import Codata.Musical.Costring 
open import Codata.Musical.Colist 
  renaming (length to length*) 
  renaming (map to map*) 
  renaming ([_] to [_]*) 
  renaming (_∷_ to _∷*_) 
  renaming (_++_ to _++*_) 
open import Data.List
open import Data.Char
open import Data.Bool
open import Data.Product
open import Data.Maybe
  renaming (_>>=_ to _?>=_)
open import IO
  renaming (_>>=_ to _i>=_)
  renaming (_>>_ to _i>_)
open import basic

IOF : Set → Set₁
IOF A = IO (Maybe A)

_>>=_ : {A : Set} {B : Set} → IOF A → (A → IOF B) → IOF B
_>>=_ f g = ♯ f i>= \ { 
    nothing → ♯ (return nothing)
  ; (just x) → ♯ (g x)
  }
  
_>>_ : {A : Set} {B : Set} → IOF A → IOF B → IOF B
_>>_ f g = ♯ f i>= \ { 
    nothing → ♯ (return nothing)
  ; (just _) → ♯ g 
  }

ret : ∀ {A} → A → IOF A 
ret a = return (just a)

fin : ∀ {A} → IOF A 
fin = return nothing

iof-char : Costring → IOF (Char × Costring)
iof-char (c ∷* ics) = ret (c , ♭ ics)
iof-char []* = fin

{-# NON_TERMINATING #-}
iof-chars : Costring → IOF (Chars × Costring)
iof-chars ('%' ∷* ics) = ret ([] , ♭ ics)
iof-chars (c ∷* ics) = do 
  (s , cs)  ← iof-chars (♭ ics)
  ret ((c ∷ s) , cs) 
iof-chars []* = fin

iof-af : Costring → IOF ((Chars × Form) × Costring)
iof-af cs = do 
  (n , cs0) ← iof-chars cs
  ('T' , cs1) ← iof-char cs0
    where _ → fin
  -- (f , cs2) ← iof-form cs1
  ('T' , cs1) ← iof-char cs0
    where _ → fin
  ret ((n , cst true) , cs3)

{-# NON_TERMINATING #-}
iof-prob : Costring → IOF (Prob × Costring)
iof-prob ('.' ∷* ics) = return (just ([] , ♭ ics))
iof-prob (',' ∷* ics) = do 
  ((n , f), cs0) ← iof-af (♭ ics)
  (P , cs1) ← iof-prob cs0
  ret ((n , f) ∷ P , cs1) 
iof-prob _ = fin
