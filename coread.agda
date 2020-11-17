open import Data.Maybe.Base 
  renaming (_>>=_ to _?>=_)
  renaming (map to map?)
open import Data.Product
open import Data.Bool
  renaming (not to bnot)
open import Data.Char
  renaming (_==_ to _=c_)
open import Agda.Builtin.Nat
open import Data.List
  renaming (or to disj)
  renaming (and to conj)
open import Codata.Musical.Costring 
open import Codata.Musical.Colist 
  renaming (length to length*) 
  renaming (map to map*) 
  renaming ([_] to [_]*) 
  renaming (_∷_ to _∷*_) 
  renaming (_++_ to _++*_) 
open import Agda.Builtin.Coinduction
open import basic

Coread : Set → Set
Coread A = Costring → Maybe (A × Costring)

_>>=_ : ∀ {A} {B} → Coread A → (A → Coread B) → Coread B
_>>=_ f g cs with f cs 
... | nothing = nothing
... | just (a , cs') = g a cs'

_>>_ : ∀ {A} {B} → Coread A → Coread B → Coread B
_>>_ f g cs with f cs 
... | nothing = nothing
... | just (_ , cs') = g cs'

copass : {A : Set} → A → Coread A
copass x cs = just (x , cs) 

cofail : {A : Set} → Coread A
cofail _ = nothing 

coread-bool : Coread Bool
coread-bool ('T' ∷* ics) = just (true , ♭ ics) 
coread-bool ('F' ∷* ics) = just (false , ♭ ics) 
coread-bool _ = nothing

coread-char : Coread Char
coread-char (c ∷* cs) = just (c , ♭ cs)
coread-char _ = nothing

{-# NON_TERMINATING #-}
coread-chars : Coread Chars
coread-chars ('%' ∷* ics) = just ([] , ♭ ics)
coread-chars (c ∷* ics) = ( do 
  cs ← coread-chars
  copass (c ∷ cs) ) (♭ ics)
coread-chars []* = nothing

colift-maybe : {A : Set} → Maybe A → Coread A
colift-maybe nothing = cofail
colift-maybe (just a) = copass a

coread-nat : Coread Nat
coread-nat = do
  cs ← coread-chars 
  colift-maybe (chars-to-nat cs)

coread-ftr-aux : Char → Coread Ftr
coread-ftr-aux '#' = do 
  k ← coread-nat 
  copass (nf k)
coread-ftr-aux '"' = do 
  cs ← coread-chars 
  copass (sf cs)
coread-ftr-aux _ = cofail

coread-ftr : Coread Ftr
coread-ftr = coread-char >>= coread-ftr-aux

{-# NON_TERMINATING #-}
coread-termoid : ∀ b → Coread (Termoid b)
coread-termoid true ('.' ∷* ics) = just (nil , ♭ ics)
coread-termoid true (',' ∷* ics) = ( do 
  t ← coread-termoid false
  ts ← coread-termoid true
  copass (cons t ts) ) (♭ ics)
coread-termoid false ('#' ∷* ics) = ( do
  k ← coread-nat 
  copass (var k) ) (♭ ics)
coread-termoid false ('$' ∷* ics) = ( do
  f ← coread-ftr 
  ts ← coread-termoid true 
  copass (fun f ts) ) (♭ ics)
coread-termoid _ _ = nothing 

coread-term : Coread Term 
coread-term = coread-termoid false

coread-terms : Coread Terms 
coread-terms = coread-termoid true

{-# NON_TERMINATING #-}
coread-form : Coread Form
coread-form ('T' ∷* ics) = just (cst true , ♭ ics)
coread-form ('F' ∷* ics) = just (cst false , ♭ ics)
coread-form ('$' ∷* ics) = ( do 
  f  ← coread-ftr
  ts ← coread-terms 
  copass (rel f ts) ) (♭ ics)
coread-form ('~' ∷* ics) = ( do 
   f ← coread-form
   copass (not f) ) (♭ ics)
coread-form ('!' ∷* ics) = ( do 
   f ← coread-form
   copass (qtf false f) ) (♭ ics)
coread-form ('?' ∷* ics) = ( do 
   f ← coread-form
   copass (qtf true f) ) (♭ ics)
coread-form ('|' ∷* ics) = ( do 
   f ← coread-form
   g ← coread-form
   copass (bct or f g) ) (♭ ics)
coread-form ('&' ∷* ics) = ( do 
   f ← coread-form
   g ← coread-form
   copass (bct and f g) ) (♭ ics)
coread-form ('>' ∷* ics) = ( do 
   f ← coread-form
   g ← coread-form
   copass (bct imp f g) ) (♭ ics)
coread-form ('=' ∷* ics) = ( do 
   f ← coread-form
   g ← coread-form
   copass (bct iff f g) ) (♭ ics)
coread-form _ = nothing

coread-af : Coread (Chars × Form) 
coread-af = do 
  n ← coread-chars 
  'T' ← coread-char 
    where _ → cofail
  f ← coread-form 
  '0' ← coread-char
    where _ → cofail
  copass (n , f) 

{-# NON_TERMINATING #-}
coread-prob : Coread Prob
coread-prob ('.' ∷* ics) = just ([] , ♭ ics)
coread-prob (',' ∷* ics) = ( do 
  (n , f) ← coread-af 
  P ← coread-prob 
  copass ((n , f) ∷ P) ) (♭ ics)
coread-prob _ = nothing