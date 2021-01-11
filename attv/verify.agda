open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
  renaming (_==_ to _=n_)
open import Function.Base
open import Data.String 
  using (String)
  using (fromChar)
  using (_++_)
  using (concat)
open import Data.Bool
  renaming (not to bnot)
  renaming (_∧_ to _&&_)
  renaming (_∨_ to _||_)
open import Data.Unit
open import Data.List
  renaming (lookup to lookup-list)
  renaming (concat to concat-list)
  renaming (_++_ to list-concat) 
  renaming (or to disj) 
  renaming (and to conj)
open import Agda.Builtin.Char
open import Data.Char
  renaming (_==_ to _=c_)
open import Data.Product
open import Data.Maybe.Base 
  renaming (_>>=_ to _o>=_)
  renaming (map to map?)
open import Agda.Builtin.Equality
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



-------- Parsers --------

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

read-af : Nat → Read Form
read-af k = do 
  _ ← read-chars 
  true ← read-bool 
    where false → fail "read-af fail : non-axiom annotated formula"
  f ← read-form k 
  '0' ← read-char 
    where _ → fail "read-af fail : non-0 endmarker" 
  pass f

Bch = Tree Form 

nth : Nat → Bch → Form 
nth k B = lookup (suc k) B ⊤*

len : Bch → Nat 
len B = pred (size B) 

read-bch-core : Nat → Bch → Read Bch
read-bch-core (suc k) B = 
  (read-spec-char '.' >> pass B) <|> 
  ( do read-spec-char ',' 
       f ← read-af k 
       -- pass-if (chk-good-form 0 f)
       read-bch-core k (add B f) )
read-bch-core 0 _ = fail "read-bch-core fail"

read-bch : Read Bch
read-bch cs = read-bch-core (length cs) (leaf ⊤*) cs

data Prf : Set where
  rule-a : Bool → Nat → Prf → Prf
  rule-b : Nat → Prf → Prf → Prf
  rule-c : Term → Nat → Prf → Prf
  rule-d : Nat → Prf → Prf
  rule-n : Nat → Prf → Prf
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



-------- Admissability Check --------

chk-good-ftr : Nat → Ftr → Bool
chk-good-ftr k (nf m) = m <n k
chk-good-ftr _ (sf _) = true

chk-good-termoid : {b : Bool} → Nat → Termoid b → Bool
chk-good-termoid k (var _) = true
chk-good-termoid k (fun f ts) = chk-good-ftr k f && chk-good-termoid k ts 
chk-good-termoid k nil = true
chk-good-termoid k (cons t ts) = chk-good-termoid k t && chk-good-termoid k ts

chk-good-term : Nat → Term → Bool
chk-good-term = chk-good-termoid 

chk-good-terms : Nat → Terms → Bool
chk-good-terms = chk-good-termoid 

chk-good-form : Nat → Form → Bool
chk-good-form k (cst _) = true
chk-good-form k (rel r ts) = chk-good-ftr k r && chk-good-terms k ts 
chk-good-form k (not f) = chk-good-form k f 
chk-good-form k (qtf _ f) = chk-good-form k f 
chk-good-form k (bct _ f g) = chk-good-form k f && chk-good-form k g

chk-gnd-termoid : {b : Bool} → Nat → Termoid b → Bool
chk-gnd-termoid k (var m) = m <n k 
chk-gnd-termoid k (fun _ ts) = chk-gnd-termoid k ts 
chk-gnd-termoid k nil = true
chk-gnd-termoid k (cons t ts) = chk-gnd-termoid k t && chk-gnd-termoid k ts

chk-gnd-term : Nat → Term → Bool
chk-gnd-term = chk-gnd-termoid 

chk-gnd-terms : Nat → Terms → Bool
chk-gnd-terms = chk-gnd-termoid 

chk-gnd-form : Nat → Form → Bool
chk-gnd-form k (cst _) = true
chk-gnd-form k (rel _ ts) = chk-gnd-terms k ts 
chk-gnd-form k (not f) = chk-gnd-form k f 
chk-gnd-form k (qtf _ f) = chk-gnd-form (suc k) f 
chk-gnd-form k (bct _ f g) = chk-gnd-form k f && chk-gnd-form k g

is_eqn : Term → Term → Form → Bool
is_eqn t s (rel (sf ('=' ∷ [])) (cons t' (cons s' nil))) = eq-term t t' && eq-term s s' 
is_eqn _ _ _ = false

refl-axiom : Form 
refl-axiom = ∀* (var 0 =* var 0)

symm-axiom : Form 
symm-axiom = ∀* (∀* ((var 1 =* var 0) →* (var 0 =* var 1)))

trans-axiom : Form 
trans-axiom = ∀* (∀* (∀* ((var 2 =* var 1) →* ((var 1 =* var 0) →* (var 2 =* var 0)))))

mono-args-lft : Nat → Terms 
mono-args-lft 0 = nil 
mono-args-lft (suc k) = cons (var (suc (k * 2))) (mono-args-lft k)

mono-args-rgt : Nat → Terms 
mono-args-rgt 0 = nil 
mono-args-rgt (suc k) = cons (var (k * 2)) (mono-args-rgt k)

chk-mono-fun : Nat → Nat → Form → Bool
chk-mono-fun k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) =
  (c =c '=') && chk-mono-fun k (suc m) f
chk-mono-fun k m (rel (sf (c ∷ [])) (cons (fun f0 ts0) (cons (fun f1 ts1) nil))) =
  (c =c '=') && chk-good-ftr (suc k) f0 && (ftr-eq f0 f1 && (terms-eq ts0 (mono-args-lft m) && terms-eq ts1 (mono-args-rgt m)))
chk-mono-fun _ _ _ = false

chk-mono-rel : Nat → Nat → Form → Bool
chk-mono-rel k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) = 
  (c =c '=') && chk-mono-rel k (suc m) f
chk-mono-rel k m (bct imp (rel r0 ts0) (rel r1 ts1)) = 
  (chk-good-ftr (suc k) r0) && (ftr-eq r0 r1) && (terms-eq ts0 (mono-args-lft m)) && (terms-eq ts1 (mono-args-rgt m))
chk-mono-rel _ _ _ = false

chk-vars-lt-termoid : ∀ {b} → Nat → Termoid b → Bool
chk-vars-lt-termoid {true} _ nil = true
chk-vars-lt-termoid {true} k (cons t ts) = 
  chk-vars-lt-termoid k t && chk-vars-lt-termoid k ts 
chk-vars-lt-termoid {false} k (var m) = m <n k
chk-vars-lt-termoid {false} k (fun _ ts) = chk-vars-lt-termoid k ts

chk-vars-lt-form : Nat → Form → Bool 
chk-vars-lt-form k (cst _) = true
chk-vars-lt-form k (not f) = chk-vars-lt-form k f
chk-vars-lt-form k (bct _ f g) = chk-vars-lt-form k f && chk-vars-lt-form k g
chk-vars-lt-form k (qtf _ f) = chk-vars-lt-form (suc k) f
chk-vars-lt-form k (rel _ ts) = chk-vars-lt-termoid k ts

chk-choice : Nat → Nat → Form → Bool
chk-choice k m (qtf false f) = chk-choice k (suc m) f
chk-choice k m (bct imp (qtf true f) g) = 
  chk-good-form k f && chk-vars-lt-form (suc m) f && 
  ( form-eq (subst-form 0 (skm-term-asc k m) f) g || 
    form-eq (subst-form 0 (skm-term-desc k m) f) g ) 
chk-choice _ _ _ = false

chk-pred-def : Nat → Nat → Form → Bool
chk-pred-def k a (qtf false f) = chk-pred-def k (suc a) f
chk-pred-def k a (bct iff (rel (nf m) ts) f) = 
  (k =n m) && (chk-good-form k f) && (chk-vars-lt-form a f) && 
    (terms-eq ts (vars-asc a) || terms-eq ts (vars-desc a))
chk-pred-def _ _ _ = false

chk-jst : Nat → Form → Bool
chk-jst k f =  
  form-eq f (cst true) ||
  form-eq f (not (cst false)) ||
  form-eq f refl-axiom ||
  form-eq f symm-axiom || 
  form-eq f trans-axiom || 
  chk-mono-rel k 0 f || 
  chk-mono-fun k 0 f || 
  chk-choice k 0 f ||
  chk-pred-def k 0 f 

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
apply-b (bct or f g) = (f , g) 
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

apply-n : Form → Form
apply-n (not (not f)) =  f
apply-n _ = ⊤*

verify : Bch → Prf → Bool
verify B (rule-a b i p) = verify (add B (apply-a b (nth i B))) p
verify B (rule-b i p q) = 
  let (g , h) = apply-b (nth i B) in
  (verify (add B g) p) && (verify (add B h) q) 
verify B (rule-c t i p) = 
  chk-good-term (suc (len B)) t && verify (add B (apply-c t (nth i B))) p
verify B (rule-d i p) = verify (add B (apply-d (len B) (nth i B))) p
verify B (rule-n i p) = verify (add B (apply-n (nth i B))) p
verify B (rule-s f p q) = 
  chk-good-form (suc (len B)) f && verify (add B (not f)) p && verify (add B f) q
verify B (rule-t f p) =
  chk-jst (len B) f && verify (add B f) p
verify B (rule-x i j) = form-eq (nth i B) (not (nth j B))

check : Chars → Chars → Bool -- Read ⊤ 
check cs-bch cs-prf with (read-bch cs-bch) , (read-prf (length cs-prf) cs-prf)
... | (cont P _) , (cont p _) = verify P p
... | _ , _ = false

{-
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


trunc-bind : ∀ {A B : Set} → (Read A) → (A → Read B) → Chars → Read B
trunc-bind f g cs with f cs
... | cont a _ = g a
... | stop s = fail s


check1 : Chars → Read ⊤ 
check1 = trunc-bind read-prob (λ P cs → verify P [] (length cs) cs)


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



-- ... | cont P _ with read-prf cs-prf 
--   ... | (cont p _) = lazy P [] p
--   ... | (stop s) = fail s 
-- 

check : Bool → Chars → Read ⊤ 
check false = check1
check true = check2
-}
