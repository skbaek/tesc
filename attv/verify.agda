open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
open import Function.Base
open import Data.String 
  using (String)
  using (fromChar)
  using (_++_)
  using (concat)
open import Data.Bool
  renaming (not to bnot)
open import Data.Unit
open import Data.List
  renaming (concat to concat-list)
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
read-bool ('0' ∷ cs) = cont false cs 
read-bool ('1' ∷ cs) = cont true cs 
read-bool _ = stop "Cannot read bool (head char neither '0' nor '1')" 

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
  pass-if (form-eq f (not g)) 

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
  b ← read-bool 
  if b
    then ( do 
      f ← read-form k
      c1 ← read-char
      if c1 ==c '0' 
        then pass (n , f)
        else fail "read-af fail : non-0 endmarker" )
    else fail "read-af fail : non-axiom annotated formula"

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

trunc-bind : ∀ {A B : Set} → (Read A) → (A → Read B) → Chars → Read B
trunc-bind f g cs with f cs
... | cont a _ = g a
... | stop s = fail s


check1 : Chars → Read ⊤ 
check1 = trunc-bind read-prob (λ P cs → verify P [] (length cs) cs)

data Prf : Set where
  rule-a : Bool → Nat → Prf → Prf
  rule-b : Nat → Prf → Prf → Prf
  rule-c : Term → Nat → Prf → Prf
  rule-d : Nat → Prf → Prf
  rule-n : Nat → Prf → Prf
  rule-p : Chars → Prf → Prf
  rule-s : Form → Prf → Prf → Prf
  rule-t : Form → Prf → Prf
  rule-x : Nat → Nat → Prf 

read-prf : Nat → Read Prf
read-prf (suc k) = 
  ( do read-spec-char 'A' 
       i ← read-nat 
       b ← read-bool 
       p ← read-prf k
       pass (rule-a b i p) ) <|> 
  ( do read-spec-char 'B' 
       i ← read-nat 
       p ← read-prf k
       q ← read-prf k
       pass (rule-b i p q) ) <|>
  ( do read-spec-char 'C' 
       i ← read-nat 
       t ← read-term k
       p ← read-prf k
       pass (rule-c t i p) ) <|>
  ( do read-spec-char 'D' 
       i ← read-nat 
       p ← read-prf k
       pass (rule-d i p) ) <|>
  ( do read-spec-char 'N' 
       i ← read-nat 
       p ← read-prf k
       pass (rule-n i p) ) <|>
  ( do read-spec-char 'P' 
       cs ← read-chars 
       p ← read-prf k
       pass (rule-p cs p) ) <|>
  ( do read-spec-char 'S' 
       f ← read-form k 
       p ← read-prf k
       q ← read-prf k
       pass (rule-s f p q) ) <|>
  ( do read-spec-char 'T' 
       f ← read-form k 
       p ← read-prf k
       pass (rule-t f p) ) <|>
  ( do read-spec-char 'X' 
       i ← read-nat 
       j ← read-nat 
       pass (rule-x i j) ) 
read-prf 0 = fail "read-prf fail"

htn-core : Nat → Nat → Bch → Form 
htn-core i (suc j) (f ∷ B) = if (i == j) then f else htn-core i j B
htn-core _ _ _ = cst true

htn : Nat → Bch → Form 
htn i B = 
  let j = length B in 
  if (i <n length B) then htn-core i j B else cst true

apply-a : Bool → Form → Form 
apply-a false  (bct and f _) =  f
apply-a true (bct and _ f) =  f
apply-a false  (not (bct or f _)) =  (not f)
apply-a true (not (bct or _ f)) =  (not f)
apply-a false  (not (bct imp f _)) =  f
apply-a true (not (bct imp _ f)) =  (not f)
apply-a false  (bct iff f g) =  (bct imp f g)
apply-a true (bct iff f g) =  (bct imp g f)
apply-a _ _ = cst true

apply-b : Form → (Form × Form)
apply-b (bct or f g) =  (f , g) 
apply-b (not (bct and f g)) =  (not f , not g) 
apply-b (bct imp f g) =  (not f , g)
apply-b (not (bct iff f g)) =  (not (bct imp f g) , not (bct imp g f))
apply-b _ = (⊤* , ⊤*)

apply-c : Term → Form → Form
apply-c t (qtf false f) =  (subst-form 0 t f)
apply-c t (not (qtf true f)) =  (not (subst-form 0 t f))
apply-c _ _ = ⊤*

apply-d : Nat → Form → Form
apply-d k (qtf true f) =  (subst-form 0 (par k) f)
apply-d k (not (qtf false f)) =  (not (subst-form 0 (par k) f))
apply-d _ _ = ⊤*

res-and : Res ⊤ → Res ⊤ → Res ⊤
res-and (cont _ cs) (cont _ _) = cont tt cs
res-and (stop s) _ = stop s
res-and (cont _ _) (stop s) = stop s

lookup-prob : Chars → Prob → Form
lookup-prob cs [] = ⊤*
lookup-prob cs ((nm , f) ∷ P) = 
  if (chars-eq nm cs) then f else lookup-prob cs P 

apply-n : Form → Form
apply-n (not (not f)) =  f
apply-n _ = ⊤*

lazy : Prob → Bch → Prf → Res ⊤  
lazy P B (rule-a b i p) = lazy P ((apply-a b (htn i B)) ∷ B) p
lazy P B (rule-b i p q) = 
  let (g , h) = apply-b (htn i B) in
  res-and (lazy P (g ∷ B) p) (lazy P (h ∷ B) q)
lazy P B (rule-c t i p) = lazy P ((apply-c t (htn i B)) ∷ B) p
lazy P B (rule-d i p) = lazy P ((apply-d (length B) (htn i B)) ∷ B) p
lazy P B (rule-n i p) = lazy P ((apply-n (htn i B)) ∷ B) p
lazy P B (rule-p cs p) = lazy P ((lookup-prob cs P) ∷ B) p
lazy P B (rule-s f p q) = 
  res-and (lazy P ((not f) ∷ B) p) (lazy P (f ∷ B) q)
lazy P B (rule-t f p) = lazy P (f ∷ B) p
lazy P B (rule-x i j) = 
  if (form-eq (htn i B) (not (htn j B)))
    then (cont tt [])
    else (stop (concat (pp-form (htn i B) ∷ " != " ∷  (pp-form (not (htn j B))) ∷ [])))

check2 : Chars → Read ⊤ 
check2 cs-prob cs-prf with (read-prob cs-prob) , (read-prf (length cs-prf) cs-prf)
... | (stop s) , _ = stop s 
... | (cont _ _) , (stop s) = stop s 
... | (cont P _) , (cont p _) = lazy P [] p

-- ... | cont P _ with read-prf cs-prf 
--   ... | (cont p _) = lazy P [] p
--   ... | (stop s) = fail s 
-- 

check : Bool → Chars → Read ⊤ 
check false = check1
check true = check2