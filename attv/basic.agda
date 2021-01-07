module basic where

open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
  renaming (_==_ to _=n_)
open import Data.Nat.DivMod
open import Agda.Builtin.Equality
open import Data.Bool
  renaming (T to tr)
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
open import Relation.Nullary 
open import Data.Product
  renaming (map to map2)
open import Data.Unit  
open import Data.Maybe
  renaming (_>>=_ to _?>=_)
  renaming (map to map?)
open import Data.Nat.Show
open import Data.Empty
open import Relation.Nullary.Decidable using (toWitness)

postulate LEM : (A : Set) → Dec A
postulate FX : ∀ {A B : Set} (f g : A → B) (h : ∀ a → f a ≡ f a) → f ≡ g

elim-lem : ∀ (A : Set) {B : Set} → (A → B) → ((¬ A) → B) → B
elim-lem A h0 h1 with LEM A 
... | (yes h2) = h0 h2
... | (no h2)  = h1 h2

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

_=*_ : Term → Term → Form
t =* s = rel (sf ('=' ∷ [])) (cons t (cons s nil))

_→*_ : Form → Form → Form
f →* g = bct imp f g

_↔*_ : Form → Form → Form
f ↔* g = bct iff f g

∀* = qtf false
∃* = qtf true

⊤* = cst true
⊥* = cst false

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
break-a false  (bct and f _) = just f
break-a true (bct and _ f) = just f
break-a false  (not (bct or f _)) = just (not f)
break-a true (not (bct or _ f)) = just (not f)
break-a false  (not (bct imp f _)) = just f
break-a true (not (bct imp _ f)) = just (not f)
break-a false  (bct iff f g) = just (bct imp f g)
break-a true (bct iff f g) = just (bct imp g f)
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

_⇔_ : Bool → Bool → Bool 
true ⇔ true = true
false ⇔ false = true
_ ⇔ _  = false

bct-eq : Bct → Bct → Bool
bct-eq or or = true
bct-eq and and = true
bct-eq imp imp = true
bct-eq iff iff = true
bct-eq _ _ = false

chars-eq : Chars → Chars → Bool
chars-eq [] [] = true
chars-eq (c0 ∷ cs0) (c1 ∷ cs1) = (c0 =c c1) && (chars-eq cs0 cs1)
chars-eq _ _ = false

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

eq-list : {A : Set} → (A → A → Bool) → List A → List A → Bool
eq-list f [] [] = true
eq-list f (x1 ∷ xs1) (x2 ∷ xs2) = f x1 x2 && (eq-list f xs1 xs2)
eq-list f _ _ = false

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

just-if : Bool → Maybe ⊤ 
just-if true = just tt
just-if false = nothing

suc-inj : ∀ {a b : Nat} → (suc a ≡ suc b) → a ≡ b
suc-inj refl = refl

just-inj : ∀  {A : Set} {a b : A} → (just a ≡ just b) → a ≡ b
just-inj refl = refl

id : ∀ {l} {A : Set l} → A → A 
id x = x

elim-eq : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → p x → x ≡ y → p y 
elim-eq p h0 refl = h0

eq-elim : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p x → p y 
eq-elim p refl = id

eq-elim-symm : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p y → p x 
eq-elim-symm p refl = id

eq-elim-2 : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} (p : A → B → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → p a0 b0 → p a1 b1 
eq-elim-2 p refl refl = id

eq-elim-3 : ∀ {A B C : Set} {a0 a1 : A} {b0 b1 : B} {c0 c1 : C} (p : A → B → C → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → c0 ≡ c1 → p a0 b0 c0 → p a1 b1 c1
eq-elim-3 p refl refl refl = id

eq-elim-4 : ∀ {A B C D : Set} {a0 a1 : A} {b0 b1 : B} 
  {c0 c1 : C} {d0 d1 : D} (p : A → B → C → D → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → c0 ≡ c1 → d0 ≡ d1 → p a0 b0 c0 d0 → p a1 b1 c1 d1
eq-elim-4 p refl refl refl refl = id

eq-trans : ∀ {A : Set} {x : A} (y : A) {z : A} → x ≡ y → y ≡ z → x ≡ z
eq-trans _ refl refl = refl

eq-symm : ∀ {A : Set} {x : A} {y : A} → x ≡ y → y ≡ x
eq-symm refl = refl

data _<_ : Nat → Nat → Set where
  0< : ∀ k → 0 < (suc k)
  suc< : ∀ k m → k < m → suc k < suc m

_>_ : Nat → Nat → Set 
k > m = m < k

infixr 20 _∧_ 
_∧_ = _×_

infixr 20 _∨_ 
data _∨_ : Set → Set → Set where
  or-lft  : ∀ {A B : Set} → A → A ∨ B
  or-rgt : ∀ {A B : Set} → B → A ∨ B

∨-comm : ∀ {A B} → A ∨ B → B ∨ A
∨-comm (or-lft h) = or-rgt h
∨-comm (or-rgt h) = or-lft h

_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

and-symm : ∀ {A B : Set} → (A ∧ B) → (B ∧ A)
and-symm h = snd h , fst h

or-elim : ∀ {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
or-elim (or-lft x) f g = f x
or-elim (or-rgt x) f g = g x

or-elim' : ∀ {A B C : Set} → (A → C) → (B → C) → (A ∨ B) → C
or-elim' ha hb hab = or-elim hab ha hb

ex-elim : ∀ {A B : Set} {P : A → Set} → (∃ P) → (∀ (x : A) → P x → B) → B
ex-elim (a , h0) h1 = h1 a h0

ex-elim-2 : ∀ {A B C : Set} {P : A → B → Set} → 
  (∃ λ a → ∃ (P a)) → (∀ (x : A) (y : B) → P x y → C) → C
ex-elim-2 (a , (b , h0)) h1 = h1 a b h0

ex-elim-3 : ∀ {A B C D : Set} {P : A → B → C → Set} → 
  (∃ λ a → ∃ λ b → ∃ λ c → (P a b c)) → (∀ a b c → P a b c → D) → D
ex-elim-3 (a , (b , (c , h0))) h1 = h1 a b c h0

ex-elim' : ∀ {A B : Set} {P : A → Set} → (∀ (x : A) → P x → B) → (∃ P) → B
ex-elim' h0 (a , h1) = h0 a h1

ex-elim-3' : ∀ {A B C D : Set} {P : A → B → C → Set} → 
  (∀ a b c → P a b c → D) → (∃ λ a → ∃ λ b → ∃ λ c → (P a b c)) → D
ex-elim-3' h0 (a , (b , (c , h1))) = h0 a b c h1

_∈_ : {A : Set} → A → List A → Set
a0 ∈ [] = ⊥ 
a0 ∈ (a1 ∷ as) = (a0 ≡ a1) ∨ (a0 ∈ as)


pall : {A : Set} → (A → Set) → List A → Set
pall {A} p l = ∀ (x : A) →  (x ∈ l) → p x

pall-nil : {A : Set} {p : A → Set} → pall p []
pall-nil {A} {p} x = ⊥-elim

rt : Set → Bool
rt A = elim-lem A (λ _ → true) (λ _ → false)

tr-rt-iff : ∀ {A : Set} → tr (rt A) ↔ A 
tr-rt-iff {A} with LEM A 
... | (yes h0) = (λ _ → h0) , (λ _ → tt)
... | (no h0) = ⊥-elim , h0

fs : Bool → Set
fs true  = ⊥
fs false = ⊤

cong :
  {A : Set}
  {B : Set}
  (f : A → B)
  {x y : A}
  (p : x ≡ y)
  → -----------
  f x ≡ f y
cong _ refl = refl

cong-2 :
  {A B C : Set}
  (f : A → B → C)
  {x y : A}
  {z w : B}
  (p : x ≡ y)
  (q : z ≡ w)
  → -----------
  f x z ≡ f y w
cong-2 _ refl refl = refl

cong-3 : ∀ {A B C D : Set} (f : A → B → C → D) 
  {a0 a1 : A} {b0 b1 : B} {c0 c1 : C} → a0 ≡ a1 → b0 ≡ b1 → c0 ≡ c1 → f a0 b0 c0 ≡ f a1 b1 c1
cong-3  f refl refl refl = refl 

elim-bool-absurd : ∀ {b : Bool} {A : Set} → tr b → fs b → A 
elim-bool-absurd {true} _ ()
elim-bool-absurd {false} ()

trichotomy : ∀ k m → ((k < m) ∨ ((k ≡ m) ∨ (k > m)))
trichotomy 0 0 = or-rgt (or-lft refl)
trichotomy 0 (suc m) = or-lft (0< _)
trichotomy (suc k) 0 = or-rgt (or-rgt (0< _))
trichotomy (suc k) (suc m) = 
  or-elim (trichotomy k m) 
    (\ h0 → or-lft (suc< _ _ h0)) 
    \ h0 → or-elim h0 
      (\ h1 → or-rgt (or-lft (cong suc h1))) 
      \ h1 → or-rgt (or-rgt (suc< _ _ h1))

lt-to-nat-lt : ∀ k m → k < m → tr (k <n m) 
lt-to-nat-lt 0 (suc m) (0< m) = tt
lt-to-nat-lt (suc k) (suc m) (suc< k m h) = lt-to-nat-lt k m h

nat-lt-to-lt : ∀ k m → tr (k <n m) → k < m
nat-lt-to-lt _ 0  ()
nat-lt-to-lt 0 (suc m) _ = 0< m 
nat-lt-to-lt (suc k) (suc m) h = suc< k m (nat-lt-to-lt k m h)

eq-to-nat-eq : ∀ k m → k ≡ m → tr (k =n m) 
eq-to-nat-eq 0 0 refl = tt
eq-to-nat-eq (suc k) (suc m) h = eq-to-nat-eq k m (suc-inj h) 

nat-eq-to-eq : ∀ {k m : Nat} → tr (k =n m) → k ≡ m
nat-eq-to-eq {0} {0} _ = refl
nat-eq-to-eq {0} {suc m} ()
nat-eq-to-eq {suc k} {0} ()
nat-eq-to-eq {suc k} {suc m} h = cong suc (nat-eq-to-eq h)
  
lt-to-lt-suc : ∀ (k : Nat) (m : Nat) → (k < m) → (k < (suc m))
lt-to-lt-suc 0 m _ = 0< _
lt-to-lt-suc (suc k) 0 ()
lt-to-lt-suc (suc k) (suc m) (suc< k m h) = suc< k _ (lt-to-lt-suc k m h)

not-lt-self : ∀ k → ¬ (k < k)
not-lt-self 0 ()
not-lt-self (suc k) (suc< m m h) = not-lt-self k h

lt-to-not-eq : ∀ k m → k < m → ¬ (k ≡ m)
lt-to-not-eq k m h0 h1 = not-lt-self m (eq-elim (λ x → x < m) h1 h0)

lt-to-not-gt : ∀ k m → k < m → ¬ (k > m)
lt-to-not-gt 0 0 ()
lt-to-not-gt 0 (suc k) _ ()
lt-to-not-gt (suc k) 0 ()
lt-to-not-gt (suc k) (suc m) (suc< _ _ h0) (suc< _ _ h1) = lt-to-not-gt _ _ h0 h1

intro-ite-lem : ∀ {A : Set} {x y : A} (b : Bool) → 
  (P : A → Set) → (tr b → P x) → (fs b → P y) → P (if b then x else y)
intro-ite-lem false P hx hy = hy tt
intro-ite-lem true  P hx hy = hx tt

not-or-lft : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ A 
not-or-lft h0 h1 = h0 (or-lft h1)  

not-or-rgt : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ B 
not-or-rgt h0 h1 = h0 (or-rgt h1)  

not-imp-lft : ∀ {A B : Set} → ¬ (A → B) → A 
not-imp-lft {A} {B} h0 = elim-lem  A id \ h1 → ⊥-elim (h0 \ h2 → ⊥-elim (h1 h2))

not-imp-rgt : ∀ {A B : Set} → ¬ (A → B) → ¬ B 
not-imp-rgt {A} {B} h0 h1 = ⊥-elim (h0 \ h2 → h1)

imp-to-not-or :  ∀ {A B} → (A → B) → ((¬ A) ∨ B)
imp-to-not-or {A} {B} h0 = elim-lem A (\ h1 → or-rgt (h0 h1)) or-lft 

not-and-to-not-or-not :  ∀ {A B} → ¬ (A ∧ B) → ((¬ A) ∨ (¬ B))
not-and-to-not-or-not {A} {B} h0 = elim-lem A 
  (\ h1 → elim-lem B (\ h2 → ⊥-elim (h0 (h1 , h2))) or-rgt) 
  or-lft

prod-inj-lft : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} → 
  (a0 , b0) ≡ (a1 , b1) → a0 ≡ a1
prod-inj-lft refl = refl

prod-inj-rgt : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} → 
  (a0 , b0) ≡ (a1 , b1) → b0 ≡ b1
prod-inj-rgt refl = refl

elim-bor : ∀ {A : Set} b1 b2 → (tr b1 → A) → (tr b2 → A) → tr (b1 || b2) → A
elim-bor true _ h0 _ h2 = h0 tt
elim-bor _ true _ h1 h2 = h1 tt

biff-to-eq : ∀ {b0 b1} → tr (b0 ⇔ b1) → (b0 ≡ b1)
biff-to-eq {true} {true} _ = refl
biff-to-eq {false} {false} _ = refl

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
    
top-iff : ∀ {P} → P → (⊤ ↔ P)
top-iff h0 = (λ _ → h0) , (λ _ → tt)

lt-suc-to-eq-or-lt : ∀ k m → k < (suc m) → (k ≡ m) ∨ (k < m)
lt-suc-to-eq-or-lt k 0 (0< 0) = or-lft refl
lt-suc-to-eq-or-lt k (suc m) (0< (suc m)) = or-rgt (0< m)
lt-suc-to-eq-or-lt (suc k) (suc m) (suc< k (suc m) h0) = 
  or-elim (lt-suc-to-eq-or-lt k m h0) 
    (λ h1 → or-lft (cong suc h1)) 
    (λ h1 →  or-rgt (suc< _ _ h1))

lt-suc-self : ∀ k → k < suc k
lt-suc-self 0 = 0< 0
lt-suc-self (suc k) = suc< k (suc k) (lt-suc-self k)

modus-tollens : ∀ {A : Set} {B : Set} → (A → B) → ¬ B → ¬ A  
modus-tollens h0 h1 h2 = ⊥-elim (h1 (h0 h2))

maybe-absurd : ∀ {A B : Set} {x : A} → nothing ≡ (just x) → B 
maybe-absurd ()

iff-to-not-iff-not : ∀ {A B} → (A ↔ B) → ((¬ A) ↔ (¬ B))
iff-to-not-iff-not h0 = 
  ( (\ ha hb → ⊥-elim (ha (snd h0 hb))) , 
    (\ hb ha → ⊥-elim (hb (fst h0 ha))) ) 

or-iff-or : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∨ B0) ↔ (A1 ∨ B1))
or-iff-or ha hb = 
  (\ h0 → or-elim h0 
    (\ h1 → (or-lft (fst ha h1))) 
    (\ h1 → (or-rgt (fst hb h1)))) , 
  (\ h0 → or-elim h0 
    (\ h1 → (or-lft (snd ha h1))) 
    (\ h1 → (or-rgt (snd hb h1)))) 

iff-symm : ∀ {A B} → (A ↔ B) → (B ↔ A) 
iff-symm h0 = (λ h1 → snd h0 h1) , (λ h1 → fst h0 h1)

iff-trans : ∀ {A} B {C} → (A ↔ B) → (B ↔ C) → (A ↔ C)
iff-trans _ h0 h1 = 
  (λ h2 → fst h1 (fst h0 h2)) , 
  (λ h2 → snd h0 (snd h1 h2))

and-iff-and : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∧ B0) ↔ (A1 ∧ B1))
and-iff-and ha hb = 
  (\ h0 → (fst ha (fst h0) , fst hb (snd h0))) , 
  (\ h0 → (snd ha (fst h0) , snd hb (snd h0)))

imp-iff-imp : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 → B0) ↔ (A1 → B1))
imp-iff-imp ha hb = 
  (\ h0 h1 → fst hb (h0 (snd ha h1))) , 
  (\ h0 h1 → snd hb (h0 (fst ha h1)))

iff-iff-iff : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ↔ B0) ↔ (A1 ↔ B1))
iff-iff-iff ha hb =  
  (λ h0 → iff-trans _ (iff-symm ha) (iff-trans _  h0 hb)) ,
  (λ h0 → iff-trans _ ha (iff-trans _ h0 (iff-symm hb)))

fa-iff-fa : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∀ a → P a) ↔ (∀ a → Q a))
fa-iff-fa h0 = ((\ h1 a → fst (h0 a) (h1 a)) , (\h1 a → snd (h0 a) (h1 a)))

ex-iff-ex : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∃ P) ↔ (∃ Q))
ex-iff-ex h0 = 
  (\ h1 → ex-elim h1 (\ a h2 → a , fst (h0 a) h2)) , 
  (\ h2 → ex-elim h2 (\ a h2 → a , snd (h0 a) h2))

dni : ∀ {A : Set} → A → (¬ (¬ A))
dni h0 h1 = h1 h0

dne : ∀ {A : Set} → (¬ ¬ A) → A 
dne {A} h0 = elim-lem A id λ h1 → ⊥-elim (h0 h1)

iff-refl : ∀ {A : Set} → (A ↔ A)
iff-refl = (id , id)

not-iff-not-to-iff : ∀ {A B} → ((¬ A) ↔ (¬ B)) → (A ↔ B)
not-iff-not-to-iff h0 = 
  (λ h1 → dne (λ h2 → snd h0 h2 h1)) ,
  (λ h1 → dne (λ h2 → fst h0 h2 h1)) 

eq-to-iff : ∀ {A : Set} (P : A → Set) (x y : A) → x ≡ y → ((P x) ↔ (P y))
eq-to-iff P x y refl = iff-refl  

eq-to-iff-2 : ∀ {A B : Set} (P : A → B → Set) (a0 a1 : A) (b0 b1 : B) → 
  a0 ≡ a1 → b0 ≡ b1 → ((P a0 b0) ↔ (P a1 b1))
eq-to-iff-2 P a0 a1 b0 b1 refl refl = iff-refl  

from-tr-bfst : ∀ a b → tr (a && b) → tr a 
from-tr-bfst true _ _ = tt

from-tr-bsnd : ∀ a b → tr (a && b) → tr b 
from-tr-bsnd _ true _ = tt
from-tr-bsnd true false ()

tr-band-to-and : ∀ a b → tr (a && b) → (tr a ∧ tr b)
tr-band-to-and true true _ = tt , tt

tr-band-to-and-3 : ∀ a b c → tr (a && b && c) → (tr a ∧ tr b ∧ tr c)
tr-band-to-and-3 true true true _ = tt , tt , tt

tr-band-to-and-4 : ∀ a b c d → tr (a && b && c && d) → (tr a ∧ tr b ∧ tr c ∧ tr d)
tr-band-to-and-4 true true true true _ = tt , tt , tt , tt

tr-band-to-and-5 : ∀ a b c d e → tr (a && b && c && d && e) → (tr a ∧ tr b ∧ tr c ∧ tr d ∧ tr e)
tr-band-to-and-5 true true true true true _ = tt , tt , tt , tt , tt

not-ex-to-fa-not : ∀ {A : Set} (P : A → Set) → (¬ ∃ P) → (∀ x → ¬ P x)
not-ex-to-fa-not P h0 a h1 = h0 (a , h1)

not-fa-to-ex-not : ∀ {A : Set} (P : A → Set) → ¬ (∀ x → P x) → ∃ λ x → ¬ P x
not-fa-to-ex-not P h0 = dne (λ h1 → h0 (λ a → dne (λ h2 → h1 (a , h2))))

not-fst : ∀ {A : Set} {B : Set} → ¬ (A ∧ B) → A → ¬ B  
not-fst h0 h1 h2 = h0 (h1 , h2)

tr-to-ite-eq : ∀ {A : Set} {b} {a0 a1 : A} → tr b → (if b then a0 else a1) ≡ a0
tr-to-ite-eq {_} {true} _ = refl  

fs-to-ite-ne : ∀ {A : Set} {b} {a0 a1 : A} → fs b → (if b then a0 else a1) ≡ a1
fs-to-ite-ne {_} {false} _ = refl  

char-eq-to-eq : ∀ c0 c1 → tr (c0 =c c1) → c0 ≡ c1 
char-eq-to-eq c0 c1 = toWitness

chars-eq-to-eq : ∀ cs0 cs1 → tr (chars-eq cs0 cs1) → cs0 ≡ cs1 
chars-eq-to-eq [] [] _ = refl
chars-eq-to-eq (c0 ∷ cs0) (c1 ∷ cs1) h0 = 
  cong-2 _∷_ 
    (toWitness (from-tr-bfst (c0 =c c1) _ h0)) 
    (chars-eq-to-eq cs0 cs1 (from-tr-bsnd _ _ h0))

elim-ite-lem : ∀ {A B : Set} (P : A → Set) (b : Bool) (a0 a1 : A) → 
  (tr b → P a0 → B) → (fs b → P a1 → B) → P (if b then a0 else a1) → B
elim-ite-lem _ true _ _ h0 _ h1 = h0 tt h1
elim-ite-lem _ false _ _ _ h0 h1 = h0 tt h1 

_≠_ : {A : Set} → A → A → Set 
x ≠ y = ¬ (x ≡ y)

nf-inj : ∀ {k m} → nf k ≡ nf m → k ≡ m 
nf-inj refl = refl

ex-falso : ∀ {A B : Set} → A → ¬ A → B
ex-falso h0 h1 = ⊥-elim (h1 h0)

append-assoc : ∀ {A : Set} (as0 as1 as2 : List A) → 
  as0 ++ (as1 ++ as2) ≡ (as0 ++ as1) ++ as2 
append-assoc [] as1 as2 = refl
append-assoc (a ∷ as0) as1 as2 = cong (_∷_ a) (append-assoc as0 as1 as2)

reverse-acc-cons : ∀ {A : Set} (as0 as1 : List A) → 
  reverseAcc as0 as1 ≡ (reverse as1) ++ as0  
reverse-acc-cons as0 [] = refl
reverse-acc-cons as0 (a ∷ as1) = 
  eq-trans _ (reverse-acc-cons (a ∷ as0) as1) 
    ( eq-trans _ (append-assoc (reverse as1) [ a ] as0) 
        ( let h0 : reverse as1 ++ [ a ] ≡ reverseAcc [ a ] as1 
              h0 = eq-symm (reverse-acc-cons [ a ] as1) in 
          cong (λ x → x ++ as0) h0 ) )

reverse-cons : ∀ {A : Set} (a : A) (as : List A) → reverse (a ∷ as) ≡ (reverse as) ∷ʳ a
reverse-cons a as = reverse-acc-cons [ a ] as 

reverse-app : ∀ {A : Set} (as0 as1 as2 : List A) → 
  reverseAcc as0 (as1 ++ as2) ≡ reverseAcc ((reverse as1) ++ as0) as2  
reverse-app as0 [] as2 = refl
reverse-app as0 (a ∷ as1) as2 = 
  eq-trans _ (reverse-app (a ∷ as0) as1 as2) 
    (cong (λ x → reverseAcc x as2) 
      (eq-trans _ (append-assoc (reverse as1) [ a ] as0) 
        (cong (λ x → x ++ as0) (eq-symm (reverse-cons a as1)))))

app-nil : ∀ {A : Set} (as : List A) → as ++ [] ≡ as
app-nil [] = refl
app-nil (a ∷ as) = cong (_∷_ a) (app-nil _)

reverse-snoc : ∀ {A : Set} (a : A) (as : List A) → reverse (as ∷ʳ a) ≡ a ∷ (reverse as)
reverse-snoc a as = eq-trans _ (reverse-app [] as [ a ]) (cong (_∷_ a) (app-nil _))

reverse-reverse : ∀ {A : Set} (as : List A) → reverse (reverse as) ≡ as
reverse-reverse [] = refl
reverse-reverse (a ∷ as) = 
  eq-trans (reverse (reverse as ∷ʳ a)) 
    (cong reverse (reverse-cons a as)) 
    ( eq-trans (a ∷ (reverse (reverse as))) 
        (reverse-snoc a (reverse as)) 
        (cong (_∷_ a) (reverse-reverse as)) )

intro-elim-lem : ∀ {A B : Set} (C : B → Set) {f : A → B} {g : (¬ A) → B} → 
  (∀ (x : A) → C (f x)) → (∀ (x : ¬ A) → C (g x)) → C (elim-lem A f g) 
intro-elim-lem {A} {B} C {f} {g} hf hg with LEM A  
... | (yes h0) = hf h0 
... | (no h0) = hg h0 

intro-elim-lem-yes : ∀ {A B : Set} (C : B → Set) {f : A → B} {g : (¬ A) → B} → 
  (∀ (x : A) → C (f x)) → A → C (elim-lem A f g) 
intro-elim-lem-yes {A} {B} C {f} {g} hf hA = intro-elim-lem C hf λ h0 → ⊥-elim (h0 hA)

not-app-eq-nil : ∀ {A : Set} (a : A) as0 as1 → (as0 ++ (a ∷ as1)) ≠ [] 
not-app-eq-nil _ [] _ ()
not-app-eq-nil _ (_ ∷ _) _ ()

cons-inj : ∀ {A : Set} (a0 a1 : A) as0 as1 → a0 ∷ as0 ≡ a1 ∷ as1 → (a0 ≡ a1) ∧ (as0 ≡ as1) 
cons-inj a0 a1 as0 as1 refl = refl , refl

snoc-inj : ∀ {A : Set} (a0 a1 : A) as0 as1 → as0 ∷ʳ a0 ≡ as1 ∷ʳ a1 → (as0 ≡ as1) ∧ (a0 ≡ a1)
snoc-inj a0 a1 [] [] refl = refl , refl
snoc-inj a0 a1 (a0' ∷ as0) [] h0 = ⊥-elim (not-app-eq-nil _ _ _ (snd (cons-inj a0' a1 _ _ h0)))
snoc-inj a0 a1 [] (a1' ∷ as1) h0 = ⊥-elim (not-app-eq-nil _ _ _ (snd (cons-inj a1' a0 _ _ (eq-symm h0))))
snoc-inj a0 a1 (a0' ∷ as0) (a1' ∷ as1) h0 = 
  let (h1 , h2) = cons-inj a0' a1' _ _ h0 in 
  let (h3 , h4) = snoc-inj a0 a1 as0 as1 h2 in 
  cong-2 _∷_ h1 h3 , h4

reverse-inj : ∀ {A : Set} (as0 as1 : List A) → reverse as0 ≡ reverse as1 → as0 ≡ as1  
reverse-inj [] [] refl = refl
reverse-inj (a0 ∷ as0) [] h0 = ⊥-elim (not-app-eq-nil _ _ _ (eq-trans _ (eq-symm (reverse-cons a0 as0)) h0))
reverse-inj [] (a1 ∷ as1) h0 = ⊥-elim (not-app-eq-nil _ _ _ (eq-symm (eq-trans _ h0 ( (reverse-cons a1 as1))))) 
reverse-inj (a0 ∷ as0) (a1 ∷ as1) h0 = 
  let h3 = eq-symm (reverse-cons a0 as0) in
  let h4 = reverse-cons a1 as1 in
  let (h1 , h2) = snoc-inj a0 a1 (reverse as0) (reverse as1) (eq-trans _ h3 (eq-trans _ h0 h4)) in 
  cong-2 _∷_ h2 (reverse-inj _ _ h1)

cong-fun-arg : ∀ {A B : Set} {x0 x1 : A → B} {y0 y1 : A} → 
  x0 ≡ x1 → y0 ≡ y1 → (x0 y0 ≡ x1 y1)
cong-fun-arg refl refl = refl

-- data Tree (A : Set) : Set where
--   leaf : A → Tree A
--   fork : Nat → Tree A → Tree A → Tree A 
-- 
-- nth : {A : Set} → Nat → Tree A → A → A
-- nth 0 (node a) _ = a 