module basic where

open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
open import Agda.Builtin.Equality
open import Data.Bool
  renaming (not to bnot)
  renaming (_∧_ to _&&_)
  renaming (_<_ to _<b_)
  renaming (_∨_ to _||_)
open import Data.Char
  renaming (_==_ to _=c_)
  renaming (_<_ to _<c_)
  renaming (show to show-char)
open import Data.String
  renaming (length to length-string)
  renaming (show to show-string)
  renaming (_<_ to _<s_)
  renaming (_==_ to _=s_)
  renaming (_++_ to _++s_)
open import Data.List 
  renaming (or to disj) 
  renaming (and to conj)
  renaming (concat to concat-list)
open import Data.List.Membership.Setoid using (_∈_) 
open import Data.Product
  renaming (map to map2)
open import Data.Unit  
open import Data.Maybe
  renaming (_>>=_ to _?>=_)
  renaming (map to map?)
open import Data.Nat.Show

Chars : Set
Chars = List Char 

pred : Nat → Nat
pred 0 = 0
pred (suc k) = k

data Ftr : Set where
  nf : Nat → Ftr
  sf : Chars → Ftr

-- _=ft_ : Ftr → Ftr → Bool
-- (nf k) =ft (nf m) = k == m  
-- (sf s) =ft (sf t) = s =cs t
-- _ =ft _ = false

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

drop-head : {A : Set} → List A → Nat → Maybe A 
drop-head [] _ = nothing 
drop-head (a ∷ _) 0 = just a 
drop-head (_ ∷ l) (suc k) = drop-head l k 

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
get-bch B k = rev-index (length B) k ?>= \ m → nth m B

tri : ∀ {A : Set} → Nat → A → A → A → Nat → A
tri k a b c m = if k <n m then a else if k == m then b else c

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

skolem-term-asc : Nat → Nat → Term
skolem-term-asc k a = fun (nf k) (vars-asc a)

skolem-term-desc : Nat → Nat → Term
skolem-term-desc k a = fun (nf k) (vars-desc a)

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

char-to-nat : Char → Maybe Nat  
char-to-nat '0' = just 0
char-to-nat '1' = just 1
char-to-nat '2' = just 2
char-to-nat '3' = just 3
char-to-nat '4' = just 4
char-to-nat '5' = just 5
char-to-nat '6' = just 6
char-to-nat '7' = just 7
char-to-nat '8' = just 8
char-to-nat '9' = just 9
char-to-nat _   = nothing

chars-to-nat-acc : Nat → List Char → Maybe Nat  
chars-to-nat-acc k [] = just k
chars-to-nat-acc k (c ∷ cs) = char-to-nat c ?>= \ m → chars-to-nat-acc ((k * 10) + m) cs

chars-to-nat : List Char → Maybe Nat  
chars-to-nat = chars-to-nat-acc 0


-- _&_ : Bool → Bool → Bool 
-- _&_ true true = true 
-- _&_ _ _ = false

-- _||_ : Bool → Bool → Bool 
-- _||_ true _ = true 
-- _||_ _ true = true
-- _||_ _ _ = false

_⇔_ : Bool → Bool → Bool 
true ⇔ true = true
false ⇔ false = true
_ ⇔ _  = false

eq-bct : Bct → Bct → Bool
eq-bct or or = true
eq-bct and and = true
eq-bct imp imp = true
eq-bct iff iff = true
eq-bct _ _ = false

-- eq-chars : Chars → Chars → Bool
-- eq-chars s t = (fromList s) =s (fromList t)

_=cs_ : Chars → Chars → Bool
[] =cs [] = true
(c0 ∷ cs0) =cs (c1 ∷ cs1) = (c0 =c c1) && (cs0 =cs cs1)
_ =cs _ = false

eq-ftr : Ftr → Ftr → Bool
eq-ftr (nf k) (nf m) = k == m
eq-ftr (sf s') (sf t') = s' =cs t'
eq-ftr _ _ = false

termoid-eq : {b1 b2 : Bool} → Termoid b1 → Termoid b2 → Bool
termoid-eq (var k) (var m) = k == m
termoid-eq (fun f ts) (fun g ss) = eq-ftr f g && termoid-eq ts ss
termoid-eq nil nil = true
termoid-eq (cons t' ts') (cons s' ss') = (termoid-eq t' s') && (termoid-eq ts' ss')
termoid-eq _ _ = false

eq-term : Term → Term → Bool
eq-term = termoid-eq 

terms-eq : Terms → Terms → Bool
terms-eq = termoid-eq 

eq-list : {A : Set} → (A → A → Bool) → List A → List A → Bool
eq-list f [] [] = true
eq-list f (x1 ∷ xs1) (x2 ∷ xs2) = f x1 x2 && (eq-list f xs1 xs2)
eq-list f _ _ = false

form-eq : Form → Form → Bool
form-eq (cst b0) (cst b1) = b0 ⇔ b1
form-eq (not f) (not g) = form-eq f g
form-eq (bct b1 f1 g1) (bct b2 f2 g2) = eq-bct b1 b2 && (form-eq f1 f2 && form-eq g1 g2)
form-eq (qtf p' f') (qtf q' g') = (p' ⇔ q') && (form-eq f' g')
form-eq (rel r1 ts1) (rel r2 ts2) = eq-ftr r1 r2 && terms-eq ts1 ts2
form-eq _ _ = false

-- pp-digit : Nat → Char
-- pp-digit 0 = '0'
-- pp-digit 1 = '1'
-- pp-digit 2 = '2'
-- pp-digit 3 = '3'
-- pp-digit 4 = '4'
-- pp-digit 5 = '5'
-- pp-digit 6 = '6'
-- pp-digit 7 = '7'
-- pp-digit 8 = '8'
-- pp-digit 9 = '9'
-- pp-digit _ = 'E'
-- 
-- pp-nat : Nat → String
-- pp-nat k = if k < 10 then [ pp-digit k ] else (pp-nat (k / 10)) ++ [ (pp-digit (k % 10)) ]
-- _∧_

pp-list-core : {A : Set} → (A → String) → List A → String 
pp-list-core f [] = "]"
pp-list-core f (x ∷ xs) = concat ("," ∷ f x ∷ pp-list-core f xs ∷ [])

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

fst : {A : Set} {B : Set} → (A × B) → A 
fst (x , _) = x 

snd : {A : Set} {B : Set} → (A × B) → B
snd (_ , y) = y

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
  (c =c '=') && chk-good-ftr k f0 && (eq-ftr f0 f1 && (terms-eq ts0 (mono-args-lft m) && terms-eq ts1 (mono-args-rgt m)))
chk-mono-fun _ _ _ = false

chk-mono-rel : Nat → Nat → Form → Bool
chk-mono-rel k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) = 
  (c =c '=') && chk-mono-rel k (suc m) f
chk-mono-rel k m (bct imp (rel r0 ts0) (rel r1 ts1)) = 
  (chk-good-ftr k r0) && (eq-ftr r0 r1) && (terms-eq ts0 (mono-args-lft m)) && (terms-eq ts1 (mono-args-rgt m))
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
  ( form-eq (subst-form 0 (skolem-term-asc k m) f) g || 
    form-eq (subst-form 0 (skolem-term-desc k m) f) g ) 
chk-choice _ _ _ = false

chk-pred-def : Nat → Nat → Form → Bool
chk-pred-def k a (qtf false f) = chk-pred-def k (suc a) f
chk-pred-def k a (bct iff (rel (nf m) ts) f) = 
  (k == m) && (chk-good-form k f) && (chk-vars-lt-form a f) && 
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

just-if : Bool → Maybe ⊤ 
just-if true = just tt
just-if false = nothing

suc-inj : ∀ {a b : Nat} → (suc a ≡ suc b) → a ≡ b
suc-inj refl = refl

just-inj : ∀  {A : Set} {a b : A} → (just a ≡ just b) → a ≡ b
just-inj refl = refl

