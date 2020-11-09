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
  renaming (_>>=_ to _o>=_)
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

get-from-prob : Prob → Chars → Read Form
get-from-prob [] _ = fail
get-from-prob ((n , f) ∷ P) cs = 
  if eq-chars n cs 
  then pass f 
  else get-from-prob P cs

_==c_ : Char → Char → Bool
_==c_ = primCharEquality

verify-a : Bch → Read Form 
verify-a B = do
  m ← read-nat 
  b ← read-bool
  lift-read (get-bch B m o>= break-a b)

verify-b : Bch → Read (Form × Form)
verify-b B = do
  m ← read-nat 
  lift-read (get-bch B m o>= break-b)

verify-c : Bch → Nat → Read Form
verify-c B k = do
  m ← read-nat 
  t ← read-term k
  -- pass-if $ check-gnd-term 0 t
  pass-if $ chk-good-term (suc (length B)) t
  lift-read (get-bch B m o>= break-c t)

verify-d : Bch → Read Form
verify-d B = do
  m ← read-nat 
  lift-read (get-bch B m o>= break-d (length B)) 

verify-n : Bch → Read Form
verify-n B = do 
  m ← read-nat 
  lift-read (get-bch B m o>= break-n)

verify-p : Prob → Bch → Read Form
verify-p P B = do
  cs ← read-chars 
  f ← get-from-prob P cs
  pass-if (chk-good-form (suc (length B)) f)
  pass f

verify-s : Bch → Nat → Read Form
verify-s B k = do 
  f ← read-form k
  pass-if (chk-good-form (suc (length B)) f)
  pass f 

verify-t : Bch → Nat → Read Form
verify-t B k = do 
  f ← read-form k
  pass-if (check-jst (length B) f)
  -- pass-if (chk-good-form (suc (length B)) f)
  pass f

verify-x : Bch → Read ⊤
verify-x B = do
  m ← read-nat 
  n ← read-nat 
  f ← lift-read (get-bch B m)
  g ← lift-read (get-bch B n)
  pass-if (eq-form (not f) g) 

elim-ite : ∀ {A B : Set} (P : A → Set) (b : Bool) (a0 a1 : A) → 
  (P a0 → B) → (P a1 → B) → P (if b then a0 else a1) → B
elim-ite _ true _ _ h0 _ h1 = h0 h1
elim-ite _ false _ _ _ h0 h1 = h0 h1

elim-ite' : ∀ {A B : Set} (P : A → Set) (b : Bool) (a0 a1 : A) → 
  P (if b then a0 else a1) → (P a0 → B) → (P a1 → B) → B
elim-ite' P b a0 a1 h h0 h1 = elim-ite P b a0 a1 h0 h1 h

intro-ite : ∀ {A : Set} {x : A} {y : A} (b : Bool) → 
  (P : A → Set) → P x → P y → P (if b then x else y)
intro-ite false P hx hy = hy
intro-ite true  P hx hy = hx
    
verify : Prob → Bch → Nat → Read ⊤ 
verify P B (suc k) (c ∷ cs) = (
    if c ==c 'A' then ( do 
      f ← verify-a B 
      verify P (f ∷ B) k 
    ) else if c ==c 'B' then ( do 
      (f , g) ← verify-b B 
      verify P (f ∷ B) k
      verify P (g ∷ B) k  
    ) else if c ==c 'C' then ( do 
      f ← verify-c B k 
      verify P (f ∷ B) k  
    ) else if c ==c 'D' then ( do 
      f ← verify-d B 
      verify P (f ∷ B) k 
    ) else if c ==c 'N' then ( do 
      f ← verify-n B
      verify P (f ∷ B) k 
    ) else if c ==c 'P' then ( do 
      f ← verify-p P B 
      verify P (f ∷ B) k 
    ) else if c ==c 'S' then ( do 
      f ← verify-s B k 
      verify P (not f ∷ B) k 
      verify P (f ∷ B) k 
    ) else if c ==c 'T' then ( do 
      f ← verify-t B k 
      verify P (f ∷ B) k 
    ) else if c ==c 'X' then (
      verify-x B 
    ) else fail
  ) cs
verify _ _ _ = fail
