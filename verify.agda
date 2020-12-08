open import Agda.Builtin.Nat
open import Function.Base
open import Data.String using (String)
open import Data.Bool
  renaming (not to bnot)
open import Data.Unit
open import Data.List
  renaming (or to disj) 
  renaming (and to conj)
open import Agda.Builtin.Char
open import Data.Product
open import Data.Maybe.Base 
  renaming (_>>=_ to _o>=_)
  renaming (map to map?)
open import basic

data Res (A : Set) : Set where
  cont : A → Chars → Res A 
  stop : String → Res A 

Read : Set → Set
Read A = Chars → Maybe (A × Chars)

infixl 20 _>>=_ 

_>>=_ : ∀ {A} {B} → Read A → (A → Read B) → Read B
_>>=_ f g cs with f cs 
... | nothing = nothing
... | just (a , cs') = g a cs'

_>>_ : ∀ {A} {B} → Read A → Read B → Read B
_>>_ f g cs with f cs 
... | nothing = nothing
... | just (_ , cs') = g cs'

infixr 20 _<|>_ 

_<|>_ : ∀ {A} → Read A → Read A → Read A
_<|>_ f g cs with f cs 
... | nothing = g cs
... | just x = just x

pass : {A : Set} → A → Read A
pass x cs = just (x , cs) 

fail : {A : Set} → Read A
fail _ = nothing 

skip : Read ⊤
skip = pass tt

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

read-char : Read Char
read-char (c ∷ cs) = just (c , cs)
read-char _ = nothing 

read-chars : Read Chars 
read-chars ('%' ∷ cs) = just ([] , cs)
read-chars (c ∷ cs) with read-chars cs 
... | just (cs0 , cs1) = just (c ∷ cs0 , cs1)
... | nothing = nothing 
read-chars [] = nothing

read-nat : Read Nat
read-nat = read-chars >>= (lift-read ∘ chars-to-nat)

_==c_ : Char → Char → Bool
_==c_ = primCharEquality

read-spec-char : Char → Read ⊤ 
read-spec-char c0 (c1 ∷ cs) = if c0 ==c c1 then just (tt , cs) else nothing
read-spec-char _ [] = nothing 

read-ftr : Read Ftr
read-ftr = 
  ( do read-spec-char '#' 
       k ← read-nat 
       pass (nf k) ) <|>
  ( do read-spec-char '"' 
       s ← read-chars 
       pass (sf s) ) 

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

read-qtf : Read Bool
read-qtf = 
  (read-spec-char '!' >> pass false) <|> (read-spec-char '?' >> pass true) 

read-bct : Read Bct
read-bct = 
  (read-spec-char '|' >> pass or) <|> 
  (read-spec-char '&' >> pass and) <|> 
  (read-spec-char '>' >> pass imp) <|> 
  (read-spec-char '=' >> pass iff) 

read-form : Nat → Read Form
read-form (suc k) = 
  ( do read-spec-char '$'
       f ← read-ftr 
       ts ← read-terms k
       pass (rel f ts) ) <|>
  ( do read-spec-char '~'
       f ← read-form k
       pass (not f) ) <|>
  ( do b ← read-qtf 
       f ← read-form k
       pass (qtf b f) ) <|>
  ( do b ← read-bct 
       f ← read-form k
       g ← read-form k
       pass (bct b f g) ) 
read-form 0 = fail


-- read-form : Nat → Read Form
-- read-form (suc k) (c ∷ cs) = (
--     if c ==c '$' then ( do
--       f ← read-ftr 
--       ts ← read-terms k
--       pass (rel f ts) 
--     ) else if c ==c '~' then ( do
--       f ← read-form k
--       pass (not f) 
--     ) else if c ==c '!' then ( do
--       f ← read-form k
--       pass (qtf false f) 
--     ) else if c ==c '?' then ( do
--       f ← read-form k
--       pass (qtf true f) 
--     ) else if c ==c '|' then ( do
--       f ← read-form k 
--       g ← read-form k 
--       pass (bct or f g)  
--     ) else if c ==c '&' then ( do
--       f ← read-form k 
--       g ← read-form k 
--       pass (bct and f g)  
--     ) else if c ==c '>' then ( do
--       f ← read-form k 
--       g ← read-form k 
--       pass (bct imp f g)  
--     ) else if c ==c '=' then ( do
--       f ← read-form k 
--       g ← read-form k 
--       pass (bct iff f g)  
--     ) else fail
--   ) cs
-- read-form _ _ = nothing

-- read-form : Nat → Read Form
-- read-form _ ('T' ∷ cs) = just (cst true , cs)  
-- read-form _ ('F' ∷ cs) = just (cst false , cs)  
-- read-form (suc k) ('$' ∷ cs) = ( do 
--   f ← read-ftr 
--   ts ← read-terms k
--   pass (rel f ts) ) cs 
-- read-form (suc k) ('~' ∷ cs) = ( do 
--   f ← read-form k
--   pass (not f) ) cs
-- read-form (suc k) ('!' ∷ cs) = ( do 
--   f ← read-form k
--   pass (qtf false f) ) cs
-- read-form (suc k) ('?' ∷ cs) = ( do 
--   f ← read-form k
--   pass (qtf true f) ) cs
-- read-form (suc k) ('|' ∷ cs) = ( do 
--   f ← read-form k 
--   g ← read-form k 
--   pass (bct or f g) ) cs 
-- read-form (suc k) ('&' ∷ cs) = ( do 
--   f ← read-form k 
--   g ← read-form k 
--   pass (bct and f g) ) cs 
-- read-form (suc k) ('>' ∷ cs) = ( do 
--   f ← read-form k 
--   g ← read-form k 
--   pass (bct imp f g) ) cs 
-- read-form (suc k) ('=' ∷ cs) = ( do 
--   f ← read-form k 
--   g ← read-form k 
--   pass (bct iff f g) ) cs 
-- read-form _ = fail

get-from-prob : Prob → Chars → Read Form
get-from-prob [] _ = fail
get-from-prob ((n , f) ∷ P) cs = 
  if (chars-eq n cs) 
  then pass f 
  else get-from-prob P cs

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
  pass-if (chk-jst (length B) f)
  pass f

verify-x : Bch → Read ⊤
verify-x B = do
  m ← read-nat 
  n ← read-nat 
  f ← lift-read (get-bch B m)
  g ← lift-read (get-bch B n)
  pass-if (form-eq (not f) g) 

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

read-af : Nat → Read (Chars × Form) 
read-af k = do 
  n ← read-chars 
  c0 ← read-char 
  if c0 ==c 'T'
    then ( do 
      f ← read-form k
      c1 ← read-char
      if c1 ==c '0' 
        then pass (n , f)
        else fail )
    else fail

-- read-af : Nat → Read (Chars × Form) 
-- read-af k = do 
--   n ← read-chars 
--   'T' ← read-char 
--     where _ → fail
--   f ← read-form k
--   '0' ← read-char
--     where _ → fail
--   pass (n , f) 

read-prob : Nat → Read Prob
read-prob (suc k) = 
  (read-spec-char '.' >> pass []) <|> 
  ( do read-spec-char ',' 
       (i , f) ← read-af k 
       pass-if (chk-good-form 0 f)
       P ← read-prob k
       pass ((i , f) ∷ P) )
read-prob 0 = fail

-- read-prob : Nat → Read Prob
-- read-prob (suc k) (c ∷ cs) = 
--   (
--     if c ==c '.' then ( 
--       pass [] 
--     ) else if c ==c ',' then ( do 
--       (nm , f) ← read-af k 
--       P ← read-prob k
--       pass ((nm , f) ∷ P) 
--     ) else fail 
--   ) cs
-- read-prob _ _ = nothing

parse-prob : Chars → Maybe Prob
parse-prob cs = (read-prob (length cs) cs) o>= (λ (P , _) → just P) 

chk-just : ∀ {A : Set} → Maybe A → Bool
chk-just (just _) = true
chk-just nothing = false

verif : Chars → Chars → Bool
verif pb-cs pf-cs = 
  chk-just ((parse-prob pb-cs) o>= (λ P → verify P [] (length pf-cs) pf-cs))
