module basic where

open import Agda.Builtin.Nat
open import Data.Nat.Show
open import Data.Bool
  renaming (not to bnot)
  renaming (_<_ to _<b_)
open import Data.Char
  renaming (_==_ to _==c_)
  renaming (_<_ to _<c_)
  renaming (show to show-char)
open import Data.String
  renaming (length to length-string)
  renaming (show to show-string)
  renaming (_<_ to _<s_)
  renaming (_==_ to _==s_)
  renaming (_++_ to _++s_)
open import Data.List 
  renaming (or to disj) 
  renaming (and to conj)
  renaming (concat to concat-list)
open import Data.List.Membership.Setoid using (_∈_) 
open import Data.Product
open import Data.Unit  
open import Data.Maybe
  renaming (_>>=_ to _?>=_)
  renaming (map to map?)

Chars : Set
Chars = List Char 

pred : Nat → Nat
pred 0 = 0
pred (suc k) = k

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
rev-index (suc l) k = if l < k then nothing else just (l - k)

get-bch : Bch → Nat → Maybe Form 
get-bch B k = rev-index (length B) k ?>= \ m → nth m B

subst-termoid : {b : Bool} → Nat → Term → Termoid b → Termoid b
subst-termoid k t (var m) = if k < m then var (pred m) else if k == m then t else (var m)
subst-termoid k t (fun f ts) = fun f (subst-termoid k t ts)
subst-termoid k t nil = nil
subst-termoid k t (cons s ts) = cons (subst-termoid k t s) (subst-termoid k t ts)

subst-term : Nat → Term → Term → Term
subst-term k t s = subst-termoid k t s 
 
subst-terms : Nat → Term → Terms → Terms
subst-terms k t ts = subst-termoid k t ts

incr-var-termoid : {b : Bool} → Termoid b → Termoid b
incr-var-termoid (var k) = var (k + 1)
incr-var-termoid (fun f ts) = fun f (incr-var-termoid ts)
incr-var-termoid nil = nil
incr-var-termoid (cons t ts) = cons (incr-var-termoid t) (incr-var-termoid ts)

incr-var-term : Term → Term
incr-var-term = incr-var-termoid

subst-form : Nat → Term → Form → Form 
subst-form k t (cst b) = cst b
subst-form k t (not f) = not (subst-form k t f)
subst-form k t (bct b f g) = bct b (subst-form k t f) (subst-form k t g)
subst-form k t (qtf q f) = qtf q (subst-form (k + 1) (incr-var-term t) f)
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

_&_ : Bool → Bool → Bool 
_&_ true true = true 
_&_ _ _ = false

_||_ : Bool → Bool → Bool 
_||_ true _ = true 
_||_ _ true = true
_||_ _ _ = false

_≃_ : Bool → Bool → Bool 
_≃_ true true = true
_≃_ false false = true
_≃_ _ _ = false

eq-bct : Bct → Bct → Bool
eq-bct or or = true
eq-bct and and = true
eq-bct imp imp = true
eq-bct iff iff = true
eq-bct _ _ = false

eq-chars : Chars → Chars → Bool
eq-chars s t = (fromList s) ==s (fromList t)

eq-ftr : Ftr → Ftr → Bool
eq-ftr (nf k) (nf m) = k == m
eq-ftr (sf s') (sf t') = eq-chars s' t'
eq-ftr _ _ = false

eq-termoid : {b1 b2 : Bool} → Termoid b1 → Termoid b2 → Bool
eq-termoid (var k) (var m) = k == m
eq-termoid (fun f ts) (fun g ss) = eq-ftr f g & eq-termoid ts ss
eq-termoid nil nil = true
eq-termoid (cons t' ts') (cons s' ss') = (eq-termoid t' s') & (eq-termoid ts' ss')
eq-termoid _ _ = false

eq-term : Term → Term → Bool
eq-term = eq-termoid 

eq-terms : Terms → Terms → Bool
eq-terms = eq-termoid 

eq-list : {A : Set} → (A → A → Bool) → List A → List A → Bool
eq-list f [] [] = true
eq-list f (x1 ∷ xs1) (x2 ∷ xs2) = f x1 x2 & (eq-list f xs1 xs2)
eq-list f _ _ = false

eq-form : Form → Form → Bool
eq-form (cst b') (cst c') = b' ≃ c'
eq-form (not f) (not g) = eq-form f g
eq-form (bct b1 f1 g1) (bct b2 f2 g2) = eq-bct b1 b2 & (eq-form f1 f2 & eq-form g1 g2)
eq-form (qtf p' f') (qtf q' g') = (p' ≃ q') & (eq-form f' g')
eq-form (rel r1 ts1) (rel r2 ts2) = eq-ftr r1 r2 & eq-terms ts1 ts2
eq-form _ _ = false

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

check-nf-ftr : Nat → Ftr → Bool
check-nf-ftr k (nf m) = m < k
check-nf-ftr _ (sf _) = true

check-nf-termoid : {b : Bool} → Nat → Termoid b → Bool
check-nf-termoid k (var _) = true
check-nf-termoid k (fun f ts) = check-nf-ftr k f & check-nf-termoid k ts 
check-nf-termoid k nil = true
check-nf-termoid k (cons t ts) = check-nf-termoid k t & check-nf-termoid k ts

check-nf-term : Nat → Term → Bool
check-nf-term = check-nf-termoid 

check-nf-terms : Nat → Terms → Bool
check-nf-terms = check-nf-termoid 

check-nf-form : Nat → Form → Bool
check-nf-form k (cst _) = true
check-nf-form k (rel r ts) = check-nf-ftr k r & check-nf-terms k ts 
check-nf-form k (not f) = check-nf-form k f 
check-nf-form k (qtf _ f) = check-nf-form k f 
check-nf-form k (bct _ f g) = check-nf-form k f & check-nf-form k g

check-gnd-termoid : {b : Bool} → Nat → Termoid b → Bool
check-gnd-termoid k (var m) = m < k 
check-gnd-termoid k (fun _ ts) = check-gnd-termoid k ts 
check-gnd-termoid k nil = true
check-gnd-termoid k (cons t ts) = check-gnd-termoid k t & check-gnd-termoid k ts

check-gnd-term : Nat → Term → Bool
check-gnd-term = check-gnd-termoid 

check-gnd-terms : Nat → Terms → Bool
check-gnd-terms = check-gnd-termoid 

check-gnd-form : Nat → Form → Bool
check-gnd-form k (cst _) = true
check-gnd-form k (rel _ ts) = check-gnd-terms k ts 
check-gnd-form k (not f) = check-gnd-form k f 
check-gnd-form k (qtf _ f) = check-gnd-form (k + 1) f 
check-gnd-form k (bct _ f g) = check-gnd-form k f & check-gnd-form k g

is_eqn : Term → Term → Form → Bool
is_eqn t s (rel (sf ('=' ∷ [])) (cons t' (cons s' nil))) = eq-term t t' & eq-term s s' 
is_eqn _ _ _ = false

refl-axiom : Form → Bool
refl-axiom (qtf false f) = is_eqn (var 0) (var 0) f
refl-axiom _ = false

symm-axiom : Form → Bool
symm-axiom (qtf false (qtf false (bct imp f g))) = is_eqn (var 1) (var 0) f & is_eqn (var 0) (var 1) g
symm-axiom _ = false

trans-axiom : Form → Bool
trans-axiom (qtf false (qtf false (qtf false (bct imp f (bct imp g h))))) = 
  is_eqn (var 2) (var 1) f & ( is_eqn (var 1) (var 0) g & is_eqn (var 2) (var 0) h )
trans-axiom _ = false

mono-args : Nat → (Terms × Terms)
mono-args 0 = (nil , nil) 
mono-args (suc k) = 
  let p = mono-args k 
  in (cons (var ((k * 2) + 1)) (fst p) , cons (var (k * 2)) (snd p))

mono-fun-core : Nat → Form → Bool
mono-fun-core k (qtf false (qtf false (bct imp (rel (sf ('=' ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) = mono-fun-core (k + 1) f
mono-fun-core k (rel (sf ('=' ∷ [])) (cons (fun f0 ts0) (cons (fun f1 ts1) nil))) = 
  let p = mono-args k 
  in eq-ftr f0 f1 & (eq-terms (fst p) ts0 & eq-terms (snd p) ts1)
mono-fun-core _ _ = false

mono-rel-core : Nat → Form → Bool
mono-rel-core k (qtf false (qtf false (bct imp (rel (sf ('=' ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) = mono-rel-core (k + 1) f
mono-rel-core k (bct imp (rel r0 ts0) (rel r1 ts1)) = 
  let p = mono-args k 
  in eq-ftr r0 r1 & (eq-terms (fst p) ts0 & eq-terms (snd p) ts1)
mono-rel-core _ _ = false

mono-rel : Form → Bool
mono-rel f = mono-rel-core 0 f

mono-fun : Form → Bool
mono-fun f = mono-fun-core 0 f

is-choice-axiom : Nat → Nat → Form → Bool
is-choice-axiom k a (qtf false f) = is-choice-axiom k (a + 1) f
is-choice-axiom k a (bct imp (qtf true f) g) = 
  check-nf-form k f & (eq-form (subst-form 0 (skolem-term-asc k a) f) g || eq-form (subst-form 0 (skolem-term-desc k a) f) g)
is-choice-axiom _ _ _ = false

is-pred-def : Nat → Nat → Form → Bool
is-pred-def k a (qtf false f) = is-pred-def k (a + 1) f
is-pred-def k a (bct iff (rel (nf m) ts) f) = 
  check-nf-form k f & ((k == m) & (eq-terms ts (vars-asc a) || eq-terms ts (vars-desc a)))
is-pred-def _ _ _ = false

justified : Nat → Form → Bool
justified _ (cst true) = true 
justified _ (not (cst false)) = true 
justified k f = disj ( refl-axiom f ∷ symm-axiom f ∷  trans-axiom f ∷ mono-rel f ∷ mono-fun f ∷ is-choice-axiom k 0 f ∷ is-pred-def k 0 f ∷ [] )

just-if : Bool → Maybe ⊤ 
just-if true = just tt
just-if false = nothing

