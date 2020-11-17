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

postulate LEM : (A : Set) → Dec A
postulate FX : ∀ {A B : Set} (f g : A → B) (h : ∀ a → f a ≡ f a) → f ≡ g

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
  ( form-eq (subst-form 0 (skolem-term-asc k m) f) g || 
    form-eq (subst-form 0 (skolem-term-desc k m) f) g ) 
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

eq-elim : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p x → p y 
eq-elim p refl = id

eq-elim' : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p y → p x 
eq-elim' p refl = id

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
  
<-to-<-suc : ∀ (k : Nat) (m : Nat) → (k < m) → (k < (suc m))
<-to-<-suc 0 m _ = 0< _
<-to-<-suc (suc k) 0 ()
<-to-<-suc (suc k) (suc m) (suc< k m h) = suc< k _ (<-to-<-suc k m h)

not-<-self : ∀ k → ¬ (k < k)
not-<-self 0 ()
not-<-self (suc k) (suc< m m h) = not-<-self k h

lt-to-not-eq : ∀ k m → k < m → ¬ (k ≡ m)
lt-to-not-eq k m h0 h1 = not-<-self m (eq-elim (λ x → x < m) h1 h0)

<-to-not-> : ∀ k m → k < m → ¬ (k > m)
<-to-not-> 0 0 ()
<-to-not-> 0 (suc k) _ ()
<-to-not-> (suc k) 0 ()
<-to-not-> (suc k) (suc m) (suc< _ _ h0) (suc< _ _ h1) = 
  <-to-not-> _ _ h0 h1

intro-ite-lem : ∀ {A : Set} {x y : A} (b : Bool) → 
  (P : A → Set) → (tr b → P x) → (fs b → P y) → P (if b then x else y)
intro-ite-lem false P hx hy = hy tt
intro-ite-lem true  P hx hy = hx tt

use-lem : ∀ (A : Set) {B : Set} → (A → B) → ((¬ A) → B) → B
use-lem A h0 h1 with LEM A 
... | (yes h2) = h0 h2
... | (no h2)  = h1 h2

not-or-lft : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ A 
not-or-lft h0 h1 = h0 (or-lft h1)  

not-or-rgt : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ B 
not-or-rgt h0 h1 = h0 (or-rgt h1)  

not-imp-lft : ∀ {A B : Set} → ¬ (A → B) → A 
not-imp-lft {A} {B} h0 = use-lem  A id \ h1 → ⊥-elim (h0 \ h2 → ⊥-elim (h1 h2))

not-imp-rgt : ∀ {A B : Set} → ¬ (A → B) → ¬ B 
not-imp-rgt {A} {B} h0 h1 = ⊥-elim (h0 \ h2 → h1)

imp-to-not-or :  ∀ {A B} → (A → B) → ((¬ A) ∨ B)
imp-to-not-or {A} {B} h0 = use-lem A (\ h1 → or-rgt (h0 h1)) or-lft 

not-and-to-not-or-not :  ∀ {A B} → ¬ (A ∧ B) → ((¬ A) ∨ (¬ B))
not-and-to-not-or-not {A} {B} h0 = use-lem A 
  (\ h1 → use-lem B (\ h2 → ⊥-elim (h0 (h1 , h2))) or-rgt) 
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
