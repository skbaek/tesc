open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
  renaming (_==_ to _=n_)
open import Function.Base
open import Data.Bool
  renaming (T to tr)
  renaming (not to bnot)
  renaming (_∧_ to _&&_)
  renaming (_<_ to _<b_)
  renaming (_∨_ to _||_)
open import Data.Unit
open import Data.List
  using (List)
  using (length)
  using ([])
  using ([_])
  using (_∷_)
  using (_++_)
open import Agda.Builtin.Char
  using (primCharEquality)
open import Data.Char
  renaming (_==_ to _=c_)
  renaming (_<_ to _<c_)
  renaming (show to show-char)
open import Data.Product
open import Data.Maybe.Base 
  renaming (_>>=_ to _o>=_)
  renaming (map to map?)
open import Data.Nat.DivMod
open import Data.String 
  using (concat)
  using (String)
  using (fromList)
open import Data.Nat.Show
open import basic

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
_==c_ : Char → Char → Bool
c0 ==c c1 = primCharEquality c0 c1

data Ftr : Set where
  nf : Nat → Ftr
  sf : Chars → Ftr

ElemList : Set → Bool → Set 
ElemList A false = A
ElemList A true = List A

data Termoid : Bool → Set where
  var : Nat → Termoid false
  fun : Ftr → Termoid true → Termoid false
  nil : Termoid true 
  cons : Termoid false → Termoid true → Termoid true

Term = Termoid false 
Terms = Termoid true

data Bct : Set where
  or  : Bct
  and : Bct
  imp : Bct
  iff : Bct

data Form : Set where
  cst : Bool → Form
  not : Form → Form
  bct : Bct → Form → Form → Form
  qtf : Bool → Form → Form 
  rel : Ftr → Terms → Form

_=*_ : Term → Term → Form
t =* s = rel (sf ('=' ∷ [])) (cons t (cons s nil))

_→*_ : Form → Form → Form
f →* g = bct imp f g

_↔*_ : Form → Form → Form
f ↔* g = bct iff f g

∀* = qtf false
∃* = qtf true

Prob : Set 
Prob = List (Chars × Form)
Bch = List Form 

par : Nat → Term
par k = fun (nf k) nil

nth : {A : Set} → Nat → List A → Maybe A 
nth 0 (x ∷ _) = just x
nth (suc k) (_ ∷ xs) = nth k xs
nth _ _ = nothing

rev-index : Nat → Nat → Maybe Nat
rev-index 0 _ = nothing
rev-index (suc l) k = if l <n k then nothing else just (l - k)

get-bch : Bch → Nat → Maybe Form 
get-bch B k = rev-index (length B) k o>= λ m → nth m B

tri : ∀ {A : Set} → Nat → A → A → A → Nat → A
tri k a b c m = if k <n m then a else if k =n m then b else c

subst-termoid : {b : Bool} → Nat → Term → Termoid b → Termoid b
subst-termoid k t (var m) = tri k (var (pred m)) t (var m) m
subst-termoid k t (fun f ts) = fun f (subst-termoid k t ts)
subst-termoid k t nil = nil
subst-termoid k t (cons s ts) = cons (subst-termoid k t s) (subst-termoid k t ts)

subst-term : Nat → Term → Term → Term
subst-term k t s = subst-termoid k t s 
 
subst-terms : Nat → Term → Terms → Terms
subst-terms k t ts = subst-termoid k t ts

incr-var : {b : Bool} → Termoid b → Termoid b
incr-var (var k) = var (suc k)
incr-var (fun f ts) = fun f (incr-var ts)
incr-var nil = nil
incr-var (cons t ts) = cons (incr-var t) (incr-var ts)

subst-form : Nat → Term → Form → Form 
subst-form k t (cst b) = cst b
subst-form k t (not f) = not (subst-form k t f)
subst-form k t (bct b f g) = bct b (subst-form k t f) (subst-form k t g)
subst-form k t (qtf q f) = qtf q (subst-form (suc k) (incr-var t) f)
subst-form k t (rel f ts) = rel f (subst-terms k t ts)

rev-terms : Terms → Terms → Terms
rev-terms nil acc = acc
rev-terms (cons t ts) acc = rev-terms ts (cons t acc)

vars-desc : Nat → Terms
vars-desc 0 = nil
vars-desc (suc k) = cons (var k) (vars-desc k)

vars-asc : Nat → Terms
vars-asc k = rev-terms (vars-desc k) nil

skm-term-asc : Nat → Nat → Term
skm-term-asc k a = fun (nf k) (vars-asc a)

skm-term-desc : Nat → Nat → Term
skm-term-desc k a = fun (nf k) (vars-desc a)

break-a : Bool → Form → Maybe Form 
break-a true  (bct and f _) = just f
break-a false (bct and _ f) = just f
break-a true  (not (bct or f _)) = just (not f)
break-a false (not (bct or _ f)) = just (not f)
break-a true  (not (bct imp f _)) = just f
break-a false (not (bct imp _ f)) = just (not f)
break-a true  (bct iff f g) = just (bct imp f g)
break-a false (bct iff f g) = just (bct imp g f)
break-a _ _ = nothing

break-b : Form → Maybe (Form × Form)
break-b (bct or f g) = just (f , g) 
break-b (not (bct and f g)) = just (not f , not g) 
break-b (bct imp f g) = just (not f , g)
break-b (not (bct iff f g)) = just (not (bct imp f g) , not (bct imp g f))
break-b _ = nothing

break-c : Term → Form → Maybe Form
break-c t (qtf false f) = just (subst-form 0 t f)
break-c t (not (qtf true f)) = just (not (subst-form 0 t f))
break-c _ _ = nothing

break-d : Nat → Form → Maybe Form
break-d k (qtf true f) = just (subst-form 0 (par k) f)
break-d k (not (qtf false f)) = just (not (subst-form 0 (par k) f))
break-d _ _ = nothing

break-n : Form → Maybe Form
break-n (not (not f)) = just f
break-n _ = nothing

bct-eq : Bct → Bct → Bool
bct-eq or or = true
bct-eq and and = true
bct-eq imp imp = true
bct-eq iff iff = true
bct-eq _ _ = false

ftr-eq : Ftr → Ftr → Bool
ftr-eq (nf k) (nf m) = k =n m
ftr-eq (sf s') (sf t') = chars-eq s' t'
ftr-eq _ _ = false

termoid-eq : {b1 b2 : Bool} → Termoid b1 → Termoid b2 → Bool
termoid-eq (var k) (var m) = k =n m
termoid-eq (fun f ts) (fun g ss) = ftr-eq f g && termoid-eq ts ss
termoid-eq nil nil = true
termoid-eq (cons t' ts') (cons s' ss') = (termoid-eq t' s') && (termoid-eq ts' ss')
termoid-eq _ _ = false

eq-term : Term → Term → Bool
eq-term = termoid-eq 

terms-eq : Terms → Terms → Bool
terms-eq = termoid-eq 
form-eq : Form → Form → Bool
form-eq (cst b0) (cst b1) = b0 ⇔ b1
form-eq (not f) (not g) = form-eq f g
form-eq (bct b1 f1 g1) (bct b2 f2 g2) = bct-eq b1 b2 && (form-eq f1 f2 && form-eq g1 g2)
form-eq (qtf p' f') (qtf q' g') = (p' ⇔ q') && (form-eq f' g')
form-eq (rel r1 ts1) (rel r2 ts2) = ftr-eq r1 r2 && terms-eq ts1 ts2
form-eq _ _ = false

pp-digit : Nat → Char
pp-digit 0 = '0'
pp-digit 1 = '1'
pp-digit 2 = '2'
pp-digit 3 = '3'
pp-digit 4 = '4'
pp-digit 5 = '5'
pp-digit 6 = '6'
pp-digit 7 = '7'
pp-digit 8 = '8'
pp-digit 9 = '9'
pp-digit _ = 'E'

{-# NON_TERMINATING #-}
pp-nat : Nat → Chars
pp-nat k = if k <n 10 then [ pp-digit k ] else (pp-nat (k / 10)) ++ [ (pp-digit (k % 10)) ]

pp-list-core : {A : Set} → (A → String) → List A → String 
pp-list-core f [] = "]"
pp-list-core f (x ∷ xs) = Data.String.concat ("," ∷ f x ∷ pp-list-core f xs ∷ [])

pp-list : {A : Set} → (A → String) → List A → String 
pp-list f [] = "[]"
pp-list f (x ∷ xs) = concat ("[" ∷ f x ∷ pp-list-core f xs ∷ [])

pp-ftr : Ftr → String 
pp-ftr (nf k) = concat ( "#" ∷ show k ∷ [] )
pp-ftr (sf s) = fromList s

pp-termoid : (b : Bool) → Termoid b → String 
pp-termoid false (var k) = concat ( "#" ∷ show k ∷ [] )
pp-termoid false (fun f ts) = concat ( pp-ftr f ∷ "(" ∷ pp-termoid true ts ∷ ")" ∷ [] )
pp-termoid true nil = ""
pp-termoid true (cons t nil) = pp-termoid false t 
pp-termoid true (cons t ts) = concat ( pp-termoid false t ∷ "," ∷ pp-termoid true ts ∷ [] )

pp-bool : Bool → String
pp-bool true = "true"
pp-bool false = "false"

pp-term = pp-termoid false
pp-terms = pp-termoid true

pp-form : Form → String 
pp-form (cst true) = "⊤"
pp-form (cst false) = "⊥"
pp-form (rel r ts) = concat ( pp-ftr r ∷ "(" ∷ pp-terms ts ∷ ")" ∷ [] )
pp-form (bct or f g) = concat ( "(" ∷ pp-form f ∷ " ∨ " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (bct and f g) = concat ( "(" ∷ pp-form f ∷ " ∧ " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (bct imp f g) = concat ( "(" ∷ pp-form f ∷ " → " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (bct iff f g) = concat ( "(" ∷ pp-form f ∷ " ↔ " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (qtf true f) = concat ( "∃ " ∷ pp-form f ∷ [] )
pp-form (qtf false f) = concat ( "∀ " ∷ pp-form f ∷ [] )
pp-form (not f) = concat ( "¬ " ∷ pp-form f ∷ [] )

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
  (c =c '=') && chk-good-ftr k f0 && (ftr-eq f0 f1 && (terms-eq ts0 (mono-args-lft m) && terms-eq ts1 (mono-args-rgt m)))
chk-mono-fun _ _ _ = false

chk-mono-rel : Nat → Nat → Form → Bool
chk-mono-rel k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) = 
  (c =c '=') && chk-mono-rel k (suc m) f
chk-mono-rel k m (bct imp (rel r0 ts0) (rel r1 ts1)) = 
  (chk-good-ftr k r0) && (ftr-eq r0 r1) && (terms-eq ts0 (mono-args-lft m)) && (terms-eq ts1 (mono-args-rgt m))
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


-- lift-0 : {A : Set} → Maybe A → Read A 
-- lift-0 nothing = fail 
-- lift-0 (just a) = pass a 
-- 
-- lift-1 : {A B : Set} → (A → Maybe B) → A → Read B
-- lift-1 f a = lift-0 (f a)
-- 
lift : {A : Set} → Maybe A → Read A 
lift nothing = fail 
lift (just a) = pass a 

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
read-nat = read-chars >>= (lift ∘ chars-to-nat)

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

get-prob : Prob → Chars → Read Form
get-prob [] _ = fail
get-prob ((n , f) ∷ P) cs = 
  if (chars-eq n cs) 
  then pass f 
  else get-prob P cs

fetch : Bch → Nat → Read Form
fetch B k = lift (get-bch B k)

verify-a : Bch → Read Form 
verify-a B = do
  m ← read-nat 
  b ← read-bool
  f ← fetch B m 
  lift (break-a b f)

verify-b : Bch → Read (Form × Form)
verify-b B = do
  m ← read-nat 
  f ← fetch B m
  lift (break-b f)

verify-c : Bch → Nat → Read Form
verify-c B k = do
  m ← read-nat 
  t ← read-term k
  pass-if $ chk-good-term (suc (length B)) t
  f ← fetch B m 
  lift (break-c t f)

verify-d : Bch → Read Form
verify-d B = do
  m ← read-nat 
  f ← fetch B m 
  lift (break-d (length B) f)

verify-n : Bch → Read Form
verify-n B = do 
  m ← read-nat 
  f ← fetch B m 
  lift (break-n f)

verify-p : Prob → Bch → Read Form
verify-p P B = read-chars >>= get-prob P

  -- f ← get-prob P cs
  -- pass-if (chk-good-form (suc (length B)) f)
  -- pass f

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
  f ← fetch B m
  g ← fetch B n
  pass-if (form-eq (not f) g) 

read-spec-char : Char → Read ⊤ 
read-spec-char c0 (c1 ∷ cs) = if c0 ==c c1 then just (tt , cs) else nothing
read-spec-char _ [] = nothing 

read-af : Nat → Read (Chars × Form) 
read-af k = do 
  i ← read-chars 
  read-spec-char 'T'
  f ← read-form k 
  read-spec-char '0'
  pass (i , f) 

read-prob : Nat → Read Prob
read-prob (suc k) = 
  (read-spec-char '.' >> pass []) <|> 
  ( do read-spec-char ',' 
       (i , f) ← read-af k 
       pass-if (chk-good-form 0 f)
       P ← read-prob k
       pass ((i , f) ∷ P) )
read-prob 0 = fail

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
