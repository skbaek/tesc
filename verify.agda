open import Agda.Builtin.Nat
open import Function.Base
open import Data.String 
  using (String)
  using (fromChar)
  using (_++_)
open import Data.Bool
  renaming (not to bnot)
open import Data.Unit
open import Data.List
  renaming (_++_ to list-concat) 
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
Read A = Chars → Res A 

infixl 20 _>>=_ 

_>>=_ : ∀ {A} {B} → Read A → (A → Read B) → Read B
_>>=_ f g cs with f cs 
... | stop msg = stop msg
... | cont a cs' = g a cs'

_>>_ : ∀ {A} {B} → Read A → Read B → Read B
_>>_ f g cs with f cs 
... | stop msg = stop msg
... | cont _ cs' = g cs'

infixr 20 _<|>_ 

_<|>_ : ∀ {A} → Read A → Read A → Read A
_<|>_ f g cs with f cs 
... | stop _ = g cs
... | c = c

pass : {A : Set} → A → Read A
pass x cs = cont x cs 

fail : {A : Set} → String → Read A
fail s _ = stop s 

skip : Read ⊤
skip = pass tt

lift-read : {A : Set} → Maybe A → Read A 
lift-read nothing = fail "Cannot lift nothing" 
lift-read (just a) = pass a 

pass-if : Bool → Read ⊤
pass-if true = pass tt
pass-if false = fail "Pass-if test failed"

read-bool : Read Bool
read-bool ('T' ∷ cs) = cont true cs 
read-bool ('F' ∷ cs) = cont false cs 
read-bool _ = stop "Cannot read bool (head char neither 'T' nor 'F')" 

read-char : Read Char
read-char (c ∷ cs) = cont c cs
read-char = fail "Cannot read char from empty string" 

read-chars : Read Chars 
read-chars ('%' ∷ cs) = cont [] cs
read-chars (c ∷ cs) with read-chars cs 
... | cont cs0 cs1 = cont (c ∷ cs0) cs1
... | st = st 
read-chars = fail "read-char fail : reached end of input string before endmarker"

read-nat : Read Nat
read-nat = read-chars >>= (lift-read ∘ chars-to-nat)

_==c_ : Char → Char → Bool
_==c_ = primCharEquality

read-spec-char : Char → Read ⊤ 
read-spec-char c0 (c1 ∷ cs) = 
  if c0 ==c c1 
    then cont tt cs 
    else stop ("char expected = " ++ fromChar c0 ++ ", char read = " ++ fromChar c1)
read-spec-char _ = fail "read-spec-char fail : reached end of input string before endmarker"

read-ftr : Read Ftr
read-ftr = 
  ( do read-spec-char '#' 
       k ← read-nat 
       pass (nf k) ) <|>
  ( do read-spec-char '"' 
       s ← read-chars 
       pass (sf s) ) 

-- just \(([A-Za-z0-9]+) , ([A-Za-z0-9]+)\)
read-termoid : ∀ b → Nat → Read (Termoid b)
read-termoid true _ ('.' ∷ cs) = cont nil cs 
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
read-termoid _ _ = fail "read-termoid fail" 

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
  ( do b ← read-bool
       pass (cst b) ) <|>
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
read-form 0 = fail "read-form fail"


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
get-from-prob [] _ = fail "get-from-prob fail"
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
    ) else fail "verify fail : invalid toplevel char"
  ) cs
verify _ _ _ = fail "verify fail : invalid case"

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
        else fail "read-af fail : non-0 endmarker" )
    else fail "read-af fail : non-axiom annotated formula"

-- read-af : Nat → Read (Chars × Form) 
-- read-af k = do 
--   n ← read-chars 
--   'T' ← read-char 
--     where _ → fail
--   f ← read-form k
--   '0' ← read-char
--     where _ → fail
--   pass (n , f) 

read-prob-core : Nat → Read Prob
read-prob-core (suc k) = 
  (read-spec-char '.' >> pass []) <|> 
  ( do read-spec-char ',' 
       (i , f) ← read-af k 
       pass-if (chk-good-form 0 f)
       P ← read-prob-core k
       pass ((i , f) ∷ P) )
read-prob-core 0 = fail "read-prob-core fail"

read-prob : Read Prob
read-prob cs = read-prob-core (length cs) cs

-- read-prob-core : Nat → Read Prob
-- read-prob-core (suc k) (c ∷ cs) = 
--   (
--     if c ==c '.' then ( 
--       pass [] 
--     ) else if c ==c ',' then ( do 
--       (nm , f) ← read-af k 
--       P ← read-prob-core k
--       pass ((nm , f) ∷ P) 
--     ) else fail 
--   ) cs
-- read-prob-core _ _ = nothing

-- parse-prob : Chars → Maybe Prob
-- parse-prob cs = (read-prob-core (length cs) cs) o>= (λ (P , _) → just P) 

-- chk-just : ∀ {A : Set} → Maybe A → Bool
-- chk-just (just _) = true
-- chk-just nothing = false

trunc-bind : ∀ {A B : Set} → (Read A) → (A → Read B) → Chars → Read B
trunc-bind f g cs with f cs
... | cont a _ = g a
... | stop s = fail s

check : Chars → Read ⊤ 
check = trunc-bind read-prob (λ P cs → verify P [] (length cs) cs)
-- ... | cont P _ = verify P [] (length pf-cs) pf-cs
-- ... | stop msg = stop msg
--  -- chk-just ((parse-prob pb-cs) o>= (λ P → verify P [] (length pf-cs) pf-cs))
