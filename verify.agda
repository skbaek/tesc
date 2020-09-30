open import Agda.Builtin.Nat
open import Function.Base
open import Data.Bool
  renaming (not to bnot)
open import Data.Unit
open import Data.List
  renaming (or to disj) 
  renaming(and to conj)
open import Agda.Builtin.Char
open import Data.Product
open import Data.Maybe.Base 
  renaming (_>>=_ to _?>=_)
  renaming (map to map?)
open import basic

Read : Set → Set
Read A = Chars → Maybe (A × Chars)

_>>=_ : ∀ {A} {B} → Read A → (A → Read B) → Read B
_>>=_ f g cs with f cs 
... | nothing = nothing
... | just (a , cs') = g a cs'

_>>_ : ∀ {A} {B} → Read A → Read B → Read B
_>>_ f g cs with f cs 
... | nothing = nothing
... | just (_ , cs') = g cs'

pass : {A : Set} → A → Read A
pass x cs = just (x , cs) 

fail : {A : Set} → Read A
fail _ = nothing 

lift-read : {A : Set} → Maybe A → Read A 
lift-read nothing = fail 
lift-read (just a) = pass a 

pass-if : Bool → Read ⊤
pass-if true = pass tt
pass-if false = fail

read-bool : Read Bool
read-bool ('T' ∷ cs) = just (true , cs) 
read-bool ('F' ∷ cs) = just (false , cs) 
read-bool _ = nothing 

read-chars : Read Chars 
read-chars ('%' ∷ cs) = just ([] , cs)
read-chars (c ∷ cs) with read-chars cs 
... | just (cs0 , cs1) = just (c ∷ cs0 , cs1)
... | nothing = nothing 
read-chars [] = nothing

read-nat : Read Nat
read-nat = read-chars >>= (lift-read ∘ chars-to-nat)

read-ftr : Read Ftr
read-ftr ('#' ∷ cs) = ( do 
  k ← read-nat
  pass (nf k) ) cs
read-ftr ('"' ∷ cs) = ( do 
  s ← read-chars
  pass (sf s) ) cs
read-ftr _ = nothing

read-termoid : ∀ b → Nat → Read (Termoid b)
read-termoid true _ ('.' ∷ cs) = just (nil , cs) 
read-termoid true (suc k) (',' ∷ cs) = ( do 
  t ← read-termoid false k 
  ts ← read-termoid true k
  pass (cons t ts) ) cs
read-termoid false _ ('#' ∷ cs) = ( do 
  k ← read-nat 
  pass (var k) ) cs 
read-termoid false (suc k) ('$' ∷ cs) = ( do 
  f ← read-ftr 
  ts ← read-termoid true k
  pass (fun f ts) ) cs 
read-termoid _ _ _ = nothing 

read-term : Nat → Read Term
read-term = read-termoid false

read-terms : Nat → Read Terms
read-terms = read-termoid true

read-form : Nat → Read Form
read-form _ ('T' ∷ cs) = just (cst true , cs)  
read-form _ ('F' ∷ cs) = just (cst false , cs)  
read-form (suc k) ('$' ∷ cs) = ( do 
  f ← read-ftr 
  ts ← read-terms k
  pass (rel f ts) ) cs 
read-form (suc k) ('~' ∷ cs) = ( do 
  f ← read-form k
  pass (not f) ) cs
read-form (suc k) ('!' ∷ cs) = ( do 
  f ← read-form k
  pass (qtf false f) ) cs
read-form (suc k) ('?' ∷ cs) = ( do 
  f ← read-form k
  pass (qtf true f) ) cs
read-form (suc k) ('|' ∷ cs) = ( do 
  f ← read-form k 
  g ← read-form k 
  pass (bct or f g) ) cs 
read-form (suc k) ('&' ∷ cs) = ( do 
  f ← read-form k 
  g ← read-form k 
  pass (bct and f g) ) cs 
read-form (suc k) ('>' ∷ cs) = ( do 
  f ← read-form k 
  g ← read-form k 
  pass (bct imp f g) ) cs 
read-form (suc k) ('=' ∷ cs) = ( do 
  f ← read-form k 
  g ← read-form k 
  pass (bct iff f g) ) cs 
read-form _ = fail
get-from-prob : Prob → Chars → Form
get-from-prob [] _ = cst true
get-from-prob ((n , f) ∷ P) cs = if eq-chars n cs then f else get-from-prob P cs

_==c_ : Char → Char → Bool
_==c_ = primCharEquality

verify : Prob → Bch → Nat → Read ⊤ 
verify P B (suc k) (c ∷ cs) = (
    if c ==c 'A' then ( do 
      m ← read-nat 
      b ← read-bool
      f ← lift-read (get-bch B m ?>= break-a b)
      verify P (f ∷ B) k ) else 
    if c ==c 'B' then ( do
      m ← read-nat 
      (f , g) ← lift-read (get-bch B m ?>= break-b)
      verify P (f ∷ B) k
      verify P (g ∷ B) k ) else  
    if c ==c 'C' then ( do
      m ← read-nat 
      t ← read-term k
      pass-if $ check-gnd-term 0 t
      pass-if $ check-nf-term ((length B) + 1) t
      f ← lift-read (get-bch B m ?>= break-c t)
      verify P (f ∷ B) k ) else 
    if c ==c 'D' then ( do
      m ← read-nat 
      f ← lift-read (get-bch B m ?>= break-d (length B))
      verify P (f ∷ B) k ) else
    if c ==c 'N' then ( do
      m ← read-nat 
      f ← lift-read (get-bch B m ?>= break-n)
      verify P (f ∷ B) k ) else
    if c ==c 'P' then ( do
      cs ← read-chars 
      pass-if (check-nf-form ((length B) + 1) (get-from-prob P cs))
      verify P (get-from-prob P cs ∷ B) k ) else
    if c ==c 'S' then ( do
      f ← read-form k
      pass-if (check-nf-form ((length B) + 1) f)
      verify P (not f ∷ B) k 
      verify P (f ∷ B) k ) else
    if c ==c 'T' then ( do
      f ← read-form k
      pass-if (justified (length B) f)
      pass-if (check-nf-form ((length B) + 1) f)
      verify P (f ∷ B) k ) else
    if c ==c 'X' then ( do
      m ← read-nat 
      n ← read-nat 
      f ← lift-read (get-bch B m)
      g ← lift-read (get-bch B n)
      pass-if (eq-form (not f) g) ) else
    fail
  ) cs
verify _ _ _ = fail
    
    
