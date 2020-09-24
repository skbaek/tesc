{-# OPTIONS --prop #-} 

module basic where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Data.List renaming (or to disj) renaming(and to conj)
open import Data.List.Membership.Setoid using (_∈_) 
open import Data.Nat.Show
open import Codata.Musical.Costring 
open import Codata.Musical.Colist 
  renaming (length to length*) 
  renaming (map to map*) 
  renaming ([_] to [_]*) 
  renaming (_∷_ to _∷*_) 
  renaming (_++_ to _++*_) 
open import Data.Unit.Base renaming (⊤ to Unit)
open import Agda.Builtin.Coinduction
open import Data.Maybe.Base 
  renaming (map to map?)
  renaming (_>>=_ to _?>=_)
open import IO
  renaming (_>>=_ to _>>>=_)
  renaming (_>>_ to _>>>_)
import IO.Primitive as Prim

postulate
  getArgs : Prim.IO (List String)
  getProgName : Prim.IO String

{-# FOREIGN GHC import qualified System.Environment as Env #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC getArgs = fmap (map Text.pack) Env.getArgs #-}
{-# COMPILE GHC getProgName = fmap Text.pack Env.getProgName #-}

IOF : Set → Set₁ 
IOF A = IO (Maybe A)

pass : {A : Set} → A → IOF A
pass a = return (just a)

fail : {A : Set} → IOF A
fail = return nothing 

_#>=_ : {A : Set} {B : Set} → IO A → (A → IO B) → IO B
_#>=_ f g = ♯ f >>>= \ x → ♯ (g x)

_#>_  : {A : Set} {B : Set} →  IO A → IO B → IO B
_#>_ f g = ♯ f >>> ♯ g 

_>>=_ : {A : Set} {B : Set} → IOF A → (A → IOF B) → IOF B 
_>>=_ f g = f #>= ( λ { nothing → return nothing ; (just x) → g x } )

_>>_ : {A : Set} {B : Set} → IOF A → IOF B → IOF B 
_>>_ f g = f >>= \ _ → g

_<|>_ : {A : Set} → IOF A → IOF A → IOF A
_<|>_ f g = f #>= \ { nothing → g ; (just x) → return (just x) }

Chars : Set
Chars = List Char 

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

rl : Set → Set  
rl A = List A → Bool

fn : Set → Set 
fn A = List A → A

Rls : Set → Set 
Rls A = Ftr → rl A 

Fns : Set → Set 
Fns A = Ftr → fn A 

Vas : Set → Set 
Vas A = Nat → A 

Prob : Set 
Prob = Chars → Form

data ⊥ : Prop where
data ⊤ : Prop where
  tt : ⊤ 

data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

data _×_×_×_ (A B C D : Set) : Set where
  ⟨_,_,_,_⟩ : A → B → C → D → A × B × C × D

data _∧_ (A B : Prop) : Prop where
  and : A → B → A ∧ B

data _∨_ (A B : Prop) : Prop where
  left : A → A ∨ B
  right : B → A ∨ B

_↔_ : Prop → Prop → Prop 
A ↔ B = (A → B) ∧ (B → A)

data Σ (A : Set) (B : A → Prop) : Prop where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

¬ : Prop → Prop
¬ A = A → ⊥
 
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} (B : A → Prop) → Prop
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∀-syntax : ∀ {A : Set} (P : A → Prop) → Prop
∀-syntax {A} P = ∀ {x : A} → P x
syntax ∀-syntax (λ x → B) = ∀[ x ] B

termoid-val : {A : Set} → Fns A → Vas A → {b : Bool} → Termoid b → ElemList A b
termoid-val _ V (var k) = V k
termoid-val F V (fun f ts) = F f (termoid-val F V ts)
termoid-val F V nil = []
termoid-val F V (cons t ts) = (termoid-val F V t) ∷ (termoid-val F V ts)

term-val : {A : Set} → Fns A → Vas A → Term → A 
term-val F V t = termoid-val F V t

terms-val : {A : Set} → Fns A → Vas A → Terms → List A 
terms-val F V ts = termoid-val F V ts

_₀↦_ : {A : Set} → Vas A → A → Vas A 
_₀↦_ V a 0 = a
_₀↦_ V a (suc k) = V k

is-true : Bool → Prop 
is-true true = ⊤ 
is-true false = ⊥ 

holds : {A : Set} → Rls A → Fns A → Vas A → Form → Prop
holds {A} R F V (cst b) = is-true b 
holds {A} R F V (not f) = ¬ (holds R F V f)
holds {A} R F V (bct or f g) = (holds R F V f) ∨ (holds R F V g)
holds {A} R F V (bct and f g) = (holds R F V f) ∧ (holds R F V g)
holds {A} R F V (bct imp f g) = (holds R F V f) → (holds R F V g)
holds {A} R F V (bct iff f g) = (holds R F V f) ↔ (holds R F V g)
holds {A} R F V (qtf false f) = ∀[ x ] holds R F (V ₀↦ x) f
holds {A} R F V (qtf true f) = ∃[ x ] holds R F (V ₀↦ x) f
holds {A} R F V (rel r ts) = is-true (R r (terms-val F V ts)) 

unsat : Prob → Prop₁
unsat P = ∀ A R F V → ∃[ n ] ¬ (holds {A} R F V (P n))

if_then_else_ : {l : Level} {A : Set l} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

drop-head : {A : Set} → List A → Nat → IOF A 
drop-head [] _ = fail 
drop-head (a ∷ _) 0 = pass a 
drop-head (_ ∷ l) (suc k) = drop-head l k 

Bch : Set 
Bch = List Form × Nat

par : Nat → Term
par k = fun (nf k) nil

get-from-bch : Bch → Nat → IOF Form 
get-from-bch ⟨ fs , 0 ⟩ i = fail
get-from-bch ⟨ fs , suc k ⟩ i = if i < (suc k) then drop-head fs (k - i) else fail

subst-termoid : {b : Bool} → Nat → Term → Termoid b → Termoid b
subst-termoid k t (var m) = if k < m then var (m - 1) else if k == m then t else (var m)
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

to-iof : {A : Set} → Maybe A → IOF A 
to-iof nothing = fail
to-iof (just a) = pass a

io-to-iof : {A : Set} → IO A → IOF A 
io-to-iof f = f #>= \ x → return (just x)

break-a : Bool → Form → IOF Form 
break-a true  (bct and f _) = pass f
break-a false (bct and _ f) = pass f
break-a true  (not (bct or f _)) = pass (not f)
break-a false (not (bct or _ f)) = pass (not f)
break-a true  (not (bct imp f _)) = pass f
break-a false (not (bct imp _ f)) = pass (not f)
break-a true  (bct iff f g) = pass (bct imp f g)
break-a false (bct iff f g) = pass (bct imp g f)
break-a _ _ = fail

break-b : Form → IOF (Form × Form)
break-b (bct or f g) = pass ⟨ f , g ⟩ 
break-b (not (bct and f g)) = pass ⟨ not f , not g ⟩ 
break-b (bct imp f g) = pass ⟨ not f , g ⟩ 
break-b (not (bct iff f g)) = pass ⟨ not (bct imp f g) , not (bct imp g f) ⟩ 
break-b _ = fail

break-c : Term → Form → IOF Form
break-c t (qtf false f) = pass (subst-form 0 t f)
break-c t (not (qtf true f)) = pass (not (subst-form 0 t f))
break-c _ _ = fail

break-d : Nat → Form → IOF Form
break-d k (qtf true f) = pass (subst-form 0 (par k) f)
break-d k (not (qtf false f)) = pass (not (subst-form 0 (par k) f))
break-d _ _ = fail

break-n : Form → IOF Form
break-n (not (not f)) = pass f
break-n _ = fail

char-to-nat : Char → IOF Nat  
char-to-nat '0' = pass 0
char-to-nat '1' = pass 1
char-to-nat '2' = pass 2
char-to-nat '3' = pass 3
char-to-nat '4' = pass 4
char-to-nat '5' = pass 5
char-to-nat '6' = pass 6
char-to-nat '7' = pass 7
char-to-nat '8' = pass 8
char-to-nat '9' = pass 9
char-to-nat _   = fail

chars-to-nat-acc : Nat → List Char → IOF Nat  
chars-to-nat-acc k [] = pass k
chars-to-nat-acc k (c ∷ cs) = do 
  m ← char-to-nat c
  chars-to-nat-acc ((k * 10) + m) cs

chars-to-nat : List Char → IOF Nat  
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
eq-chars s t = primStringEquality (primStringFromList s) (primStringFromList t)

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

ext-bch : Form → Bch → Bch
ext-bch f ⟨ fs , k ⟩ = ⟨ f ∷ fs , k + 1 ⟩ 

data Inst : Set where
  -- Non-consuming instructions
  app-a : Inst
  app-b : Inst
  app-c : Inst
  app-d : Inst
  app-n : Inst
  app-p : Inst
  app-s : Inst
  app-t : Inst
  app-x : Inst
  get-nat : Inst
  get-chars : Inst
  mk-nf : Inst
  mk-sf : Inst
  mk-var : Inst
  mk-fun : Inst
  mk-cst : Inst
  mk-not : Inst
  mk-bct : Inst
  mk-qtf : Inst
  mk-rel : Inst
  mk-nat : Inst
  mk-cons : Inst
  -- Consuming instructions
  get-bool : Inst
  get-ftr : Inst
  get-term : Inst
  get-terms : Inst
  get-form : Inst
  acc-chars : Inst

pp-inst : Inst → String
pp-inst app-a = "app-a" 
pp-inst app-b = "app-b" 
pp-inst app-c = "app-c" 
pp-inst app-d = "app-d" 
pp-inst app-n = "app-n" 
pp-inst app-p = "app-p" 
pp-inst app-s = "app-s" 
pp-inst app-t = "app-t" 
pp-inst app-x = "app-x" 
pp-inst get-nat = "get-n" 
pp-inst get-chars = "get-cs" 
pp-inst mk-nf = "mk-nf" 
pp-inst mk-sf = "mk-sf" 
pp-inst mk-var = "mk-var" 
pp-inst mk-fun = "mk-fun" 
pp-inst mk-cst = "mk-cst" 
pp-inst mk-not = "mk-not" 
pp-inst mk-bct = "mk-bct" 
pp-inst mk-qtf = "mk-qtf" 
pp-inst mk-rel = "mk-rel" 
pp-inst mk-nat = "mk-nat" 
pp-inst mk-cons = "mk-cons" 
pp-inst get-bool = "get-bool" 
pp-inst get-ftr = "get-ftr" 
pp-inst get-term = "get-term" 
pp-inst get-terms = "get-terms" 
pp-inst get-form = "get-form" 
pp-inst acc-chars = "acc-chars" 

data Arg : Set where
  bct : Bct → Arg
  chars : List Char → Arg
  bool : Bool → Arg
  ftr : Ftr → Arg
  terms : Terms → Arg
  nat : Nat → Arg
  term : Term → Arg
  form : Form → Arg

State : Set
State = Prob × List Bch × List Arg × List Inst 

put-str : String → IOF Unit
put-str s = io-to-iof (putStr s)

put-str-ln : String → IOF Unit
put-str-ln s = put-str s >> put-str "\n"

put-pad : Nat → IOF Unit
put-pad 0 = pass tt
put-pad (suc k) = put-str "  " >> put-pad k

put-str-pad : Nat → String → IOF Unit
put-str-pad n s = put-pad n >> put-str-ln s 

append-all : List String → String
append-all [] = ""
append-all (s ∷ ss) = primStringAppend s (append-all ss)

pp-list-core : {A : Set} → (A → String) → List A → String 
pp-list-core f [] = "]"
pp-list-core f (x ∷ xs) = append-all ("," ∷ f x ∷ pp-list-core f xs ∷ [])

pp-list : {A : Set} → (A → String) → List A → String 
pp-list f [] = "[]"
pp-list f (x ∷ xs) = append-all ("[" ∷ f x ∷ pp-list-core f xs ∷ [])

pp-ftr : Ftr → String 
pp-ftr (nf k) = append-all ( "#" ∷ show k ∷ [] )
pp-ftr (sf s) = primStringFromList s

pp-termoid : (b : Bool) → Termoid b → String 
pp-termoid false (var k) = append-all ( "#" ∷ show k ∷ [] )
pp-termoid false (fun f ts) = append-all ( pp-ftr f ∷ "(" ∷ pp-termoid true ts ∷ ")" ∷ [] )
pp-termoid true nil = ""
pp-termoid true (cons t nil) = pp-termoid false t 
pp-termoid true (cons t ts) = append-all ( pp-termoid false t ∷ "," ∷ pp-termoid true ts ∷ [] )

pp-bool : Bool → String
pp-bool true = "true"
pp-bool false = "false"

pp-term = pp-termoid false
pp-terms = pp-termoid true

pp-form : Form → String 
pp-form (cst true) = "⊤"
pp-form (cst false) = "⊥"
pp-form (rel r ts) = append-all ( pp-ftr r ∷ "(" ∷ pp-terms ts ∷ ")" ∷ [] )
pp-form (bct or f g) = append-all ( "(" ∷ pp-form f ∷ " ∨ " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (bct and f g) = append-all ( "(" ∷ pp-form f ∷ " ∧ " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (bct imp f g) = append-all ( "(" ∷ pp-form f ∷ " → " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (bct iff f g) = append-all ( "(" ∷ pp-form f ∷ " ↔ " ∷ pp-form g ∷ ")" ∷ [] )
pp-form (qtf true f) = append-all ( "∃ " ∷ pp-form f ∷ [] )
pp-form (qtf false f) = append-all ( "∀ " ∷ pp-form f ∷ [] )
pp-form (not f) = append-all ( "¬ " ∷ pp-form f ∷ [] )

put-head-form : List Bch → IOF Unit 
put-head-form [] = pass tt
put-head-form ( ⟨ f ∷ fs , _ ⟩ ∷ Bs ) = 
  put-str-pad (length fs) (pp-form f)
put-head-form ( ⟨ [] , _ ⟩ ∷ Bs ) = 
  put-str-ln "Invalid empty branch found." >> fail

fst : {A : Set} {B : Set} → (A × B) → A 
fst ⟨ x , _ ⟩ = x 

snd : {A : Set} {B : Set} → (A × B) → B
snd ⟨ _ , y ⟩ = y

map-iof : {A : Set} → (A → IOF Unit) → List A → IOF Unit
map-iof f [] = pass tt
map-iof f (x ∷ xs) = f x >> map-iof f xs

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

pass-if : Bool → IOF Unit 
pass-if true  = pass tt
pass-if false = fail

fa : Form → Form 
fa f = qtf false f

ex : Form → Form 
ex f = qtf true f

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
mono-args 0 = ⟨ nil , nil ⟩ 
mono-args (suc k) = 
  let p = mono-args k 
  in ⟨ cons (var ((k * 2) + 1)) (fst p) , cons (var (k * 2)) (snd p) ⟩ 

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

-- foo : Nat → Nat → Form → IOF Unit
-- foo k a (qtf false f) = foo k (a + 1) f
-- foo k a (bct imp (qtf true f) g) = do 
--   put-str "Functor number = "
--   put-str-ln (show k)
--   put-str "Arity = "
--   put-str-ln (show a)
--   put-str "Result of substitution = "
--   put-str-ln (pp-form (subst-form 0 (skolem-term-asc k a) f)) 
--   put-str "Subtitution target = "
--   put-str-ln (pp-form g)
--   fail
-- foo _ _ _ = put-str-ln "Wrong branch" >> fail

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

justified : Nat → Form -> Bool
justified _ (cst true) = true 
justified _ (not (cst false)) = true 
justified k f = disj ( refl-axiom f ∷ symm-axiom f ∷  trans-axiom f ∷ mono-rel f ∷ mono-fun f ∷ is-choice-axiom k 0 f ∷ is-pred-def k 0 f ∷ [] )


transit : Prob → List Bch → List Arg → List Inst → IOF State
transit P (B ∷ Bs) (bool b' ∷ nat n' ∷ []) (app-a ∷ []) = do
  f ← get-from-bch B n' >>= break-a b'  
  -- put-str-pad (length (fst B)) (pp-form f)
  pass ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
transit P (B ∷ Bs) (nat n' ∷ []) (app-b ∷ []) = do
  ⟨ f , g ⟩ ← get-from-bch B n' >>= break-b 
  -- put-str-pad (length (fst B)) (pp-form f)
  pass ⟨ P , ext-bch f B ∷ ext-bch g B ∷ Bs , [] , [] ⟩
transit P (B ∷ Bs) (term t' ∷ nat n' ∷ []) (app-c ∷ []) = do
  pass-if (check-gnd-term 0 t')
  pass-if (check-nf-term ((snd B) + 1) t')
  f ← get-from-bch B n' >>= break-c t' 
  -- put-str-pad (length (fst B)) (pp-form f)
  pass ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
transit P (B@(⟨ _ , k ⟩) ∷ Bs) (nat n' ∷ []) (app-d ∷ []) = do
  f ← get-from-bch B n' >>= break-d k 
  -- put-str-pad (length (fst B)) (pp-form f)
  pass ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
transit P (B ∷ Bs) (nat n' ∷ []) (app-n ∷ []) = do
  f ← get-from-bch B n' >>= break-n 
  -- put-str-pad (length (fst B)) (pp-form f)
  pass ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
transit P (B ∷ Bs) (chars cs ∷ []) (app-p ∷ []) = do
  -- put-str-pad (length (fst B)) (pp-form (P cs))
  pass-if (check-gnd-form 0 (P cs))
  pass-if (check-nf-form ((snd B) + 1) (P cs))
  pass ⟨ P , ext-bch (P cs) B ∷ Bs , [] , [] ⟩ 
transit P (B ∷ Bs) (form f ∷ []) (app-s ∷ []) = do
  -- put-str-pad (length (fst B)) (pp-form (not f))
  pass-if (check-gnd-form 0 f)
  pass-if (check-nf-form ((snd B) + 1) f)
  pass ⟨ P , ext-bch (not f) B ∷ ext-bch f B ∷ Bs , [] , [] ⟩ 
transit P (B ∷ Bs) (form f ∷ []) (app-t ∷ []) = do
  -- put-str-pad (length (fst B)) (pp-form f)
  pass-if (check-gnd-form 0 f)
  pass-if (check-nf-form ((snd B) + 1) f)
  (pass-if (justified (snd B) f) <|> (put-str-ln "T-formula not justified" >> fail))
  pass ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
transit P (B ∷ Bs) (nat n' ∷ nat p' ∷ []) (app-x ∷ []) = do
  f ← get-from-bch B p'
  g ← get-from-bch B n' 
  if eq-form (not f) g then ( pass ⟨ P , Bs , [] , [] ⟩ ) else fail
transit P Bs (As) (get-nat ∷ IS) = 
  pass ⟨ P , Bs , (chars [] ∷ As) , (acc-chars ∷ mk-nat ∷ IS) ⟩ 
transit P Bs (As) (get-chars ∷ IS) = 
  pass ⟨ P , Bs , (chars [] ∷ As) , (acc-chars ∷ IS) ⟩ 
transit P Bs (nat n' ∷ AS) (mk-var ∷ IS) = 
  transit P Bs (term (var n') ∷ AS) IS 
transit P Bs (terms ts ∷ ftr f ∷ AS) (mk-fun ∷ IS)= 
  transit P Bs (term (fun f ts) ∷ AS) IS 
transit P Bs (terms ts ∷ ftr f ∷ AS) (mk-rel ∷ IS)= do
  transit P Bs (form (rel f ts) ∷ AS) IS 
transit P Bs (bool b' ∷ AS) (mk-cst ∷ IS)= 
  transit P Bs (form (cst b') ∷ AS) IS 
transit P Bs (form f ∷ AS) (mk-not ∷ IS)= do
  transit P Bs (form (not f) ∷ AS) IS 
transit P Bs (form g' ∷ form f' ∷ bct b' ∷ AS) (mk-bct ∷ IS)= do 
  transit P Bs (form (bct b' f' g') ∷ AS) IS 
transit P Bs (form f' ∷ bool b' ∷ AS) (mk-qtf ∷ IS)= 
  transit P Bs (form (qtf b' f') ∷ AS) IS 
transit P Bs (chars cs ∷ AS) (mk-nat ∷ IS)= do
  k' ← chars-to-nat cs 
  transit P Bs (nat k' ∷ AS) IS 
transit P Bs (terms ts' ∷ term t' ∷ AS) (mk-cons ∷ IS) = 
  transit P Bs (terms (cons t' ts') ∷ AS) (IS)
transit P Bs (nat n' ∷ AS) (mk-nf ∷ IS) = 
  transit P Bs (ftr (nf n') ∷ AS) (IS)
transit P Bs (chars cs ∷ AS) (mk-sf ∷ IS) = 
  transit P Bs (ftr (sf cs) ∷ AS) IS
transit P Bs AS IS = pass ⟨ P , Bs , AS , IS ⟩ 

check : List Char → State → IOF Unit 

check _ ⟨ _ , [] , _ , _ ⟩ = pass tt 

check ('A' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule A" >> -} (transit P Bs [] (get-nat ∷ get-bool ∷ [ app-a ]) >>= check cs)
check ('B' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule B" >> -} (transit P Bs [] (get-nat ∷ [ app-b ]) >>= check cs)
check ('C' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule C" >> -} (transit P Bs [] (get-nat ∷ get-term ∷ [ app-c ]) >>= check cs)
check ('D' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule D" >> -} (transit P Bs [] (get-nat ∷ [ app-d ]) >>= check cs)
check ('N' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule N" >> -} (transit P Bs [] (get-nat ∷ [ app-n ]) >>= check cs)
check ('P' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule P" >> -} (transit P Bs [] (get-chars ∷ [ app-p ]) >>= check cs)
check ('S' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule S" >> -} (transit P Bs [] (get-form ∷ [ app-s ]) >>= check cs)
check ('T' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule T" >> -} (transit P Bs [] (get-form ∷ [ app-t ]) >>= check cs)
check ('X' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = {- put-str-ln "Rule X" >> -} (transit P Bs [] (get-nat ∷ get-nat ∷ [ app-x ]) >>= check cs)

check ('T' ∷ cs) ⟨ P , Bs , AS , get-bool ∷ IS ⟩ = transit P Bs (bool true  ∷ AS) IS >>= check cs 
check ('F' ∷ cs) ⟨ P , Bs , AS , get-bool ∷ IS ⟩ = transit P Bs (bool false ∷ AS) IS >>= check cs 

check ('#' ∷ cs) ⟨ P , Bs , AS , get-term ∷ IS ⟩ = transit P Bs AS (get-nat ∷ mk-var ∷ IS) >>= check cs 
check ('$' ∷ cs) ⟨ P , Bs , AS , get-term ∷ IS ⟩ = transit P Bs AS (get-ftr ∷ get-terms ∷ mk-fun ∷ IS) >>= check cs 

check (',' ∷ cs) ⟨ P , Bs , AS , get-terms ∷ IS ⟩ = transit P Bs AS (get-term ∷ get-terms ∷ mk-cons ∷ IS) >>= check cs 
check ('.' ∷ cs) ⟨ P , Bs , AS , get-terms ∷ IS ⟩ = do 
  -- put-str-ln (pp-list pp-inst IS)
  -- put-str-ln "Reading in nil terms"
  transit P Bs (terms nil ∷ AS) IS >>= check cs 

check ('#' ∷ cs) ⟨ P , Bs , AS , get-ftr ∷ IS ⟩ = transit P Bs AS (get-nat ∷ mk-nf ∷ IS) >>= check cs 
check ('"' ∷ cs) ⟨ P , Bs , AS , get-ftr ∷ IS ⟩ = do 
  -- put-str-ln (pp-list pp-inst IS)
  -- put-str-ln "Reading in string functor"
  transit P Bs AS (get-chars ∷ mk-sf ∷ IS) >>= check cs 

check ('T' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit P Bs (form (cst true) ∷ AS) IS >>= check cs 
check ('F' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit P Bs (form (cst false) ∷ AS) IS >>= check cs 

check ('$' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = do 
  -- put-str-ln (pp-list pp-inst IS)
  -- put-str-ln "Reading in application"
  transit P Bs AS (get-ftr ∷ get-terms ∷ mk-rel ∷ IS) >>= check cs 
check ('~' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = do 
  -- put-str-ln (pp-list pp-inst IS)
  -- put-str-ln "Reading in negation"
  transit P Bs AS (get-form ∷ mk-not ∷ IS) >>= check cs 
check ('!' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit P Bs (bool false ∷ AS) (get-form ∷ mk-qtf ∷ IS) >>= check cs 
check ('?' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit P Bs (bool true  ∷ AS) (get-form ∷ mk-qtf ∷ IS) >>= check cs 
check ('|' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit P Bs (bct or  ∷ AS) (get-form ∷ get-form ∷ mk-bct ∷ IS) >>= check cs 
check ('&' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit P Bs (bct and ∷ AS) (get-form ∷ get-form ∷ mk-bct ∷ IS) >>= check cs 
check ('>' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit P Bs (bct imp ∷ AS) (get-form ∷ get-form ∷ mk-bct ∷ IS) >>= check cs 
check ('=' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = do
  -- put-str-ln (pp-list pp-inst IS)
  -- put-str-ln "Reading in biconditinal"
  transit P Bs (bct iff ∷ AS) (get-form ∷ get-form ∷ mk-bct ∷ IS) >>= check cs 
check ('%' ∷ cs0) ⟨ P , Bs , chars cs1 ∷ AS , acc-chars ∷ IS ⟩ = do 
  -- put-str-ln (pp-list pp-inst IS)
  -- put-str "Endmarker found, read in string = "
  -- put-str-ln (primStringFromList (reverse cs1))
  transit P Bs (chars (reverse cs1) ∷ AS) IS >>= check cs0
check (c0 ∷ cs0) ⟨ P , Bs , chars cs1 ∷ AS , acc-chars ∷ IS ⟩  = transit P Bs (chars (c0 ∷ cs1) ∷ AS) (acc-chars ∷ IS) >>= check cs0

check cs ⟨ P , BS , AS , IS ⟩ = do 
  put-str "Unexpected toplevel character found, remaining proof = "
  put-str-ln (primStringFromList cs)
  put-str "Remaining instructions = "
  put-str-ln (pp-list pp-inst IS)
  fail

update-prob : Prob → Chars → Form → Prob 
update-prob P n f m = if eq-chars n m then f else P m 

empty-prob : Prob 
empty-prob _ = cst true

read-char : Costring → IOF (Char × Costring)
read-char (c ∷* cs) = pass ⟨ c , ♭ cs ⟩ 
read-char _ = fail

{-# NON_TERMINATING #-}
read-chars : Costring → Chars → IOF (Chars × Costring)
read-chars ('%' ∷* cs) bf = pass ⟨ reverse bf , ♭ cs ⟩
read-chars (c ∷* cs) bf = read-chars (♭ cs) (c ∷ bf)
read-chars _ _ = fail

{-
char-to-bct : Char → Maybe Bct 
char-to-bct '|' = just or
char-to-bct '&' = just and
char-to-bct '>' = just imp
char-to-bct '=' = just iff
char-to-bct _   = nothing

char-to-qtf : Char → Maybe Bool 
char-to-qtf '!' = just false
char-to-qtf '?' = just true
char-to-qtf _   = nothing

read-form-bct : Bct → Costring → Maybe (Form × Costring)
read-form-bct b cs0 = do 
  ⟨ f , cs1 ⟩ ← read-form cs0
  ⟨ g , cs2 ⟩ ← read-form cs1
  just ⟨ bct b f g , cs2 ⟩ 

read-form-qtf : Bool → Costring → Maybe (Form × Costring)
read-form-qtf q cs = do 
  ⟨ f , cs' ⟩ ← read-form cs
  just ⟨ qtf q f , cs' ⟩ 
  -}

read-nat : Costring → IOF (Nat × Costring)
read-nat cs0 = do
  ⟨ s , cs1 ⟩ ← read-chars cs0 []
  k ← chars-to-nat s
  pass ⟨ k , cs1 ⟩ 

read-ftr : Costring → IOF (Ftr × Costring)
read-ftr ('#' ∷* cs) = do 
  ⟨ k , cs0 ⟩ ← read-nat (♭ cs)
  pass ⟨ nf k , cs0 ⟩ 
read-ftr ('"' ∷* cs) = do 
  ⟨ s , cs0 ⟩ ← read-chars (♭ cs) []
  pass ⟨ sf s , cs0 ⟩ 
read-ftr _ = fail

{-# NON_TERMINATING #-}
read-termoid : (b : Bool) → Costring → IOF (Termoid b × Costring)
read-termoid true ('.' ∷* cs) = pass ⟨ nil , ♭ cs ⟩ 
read-termoid true (',' ∷* cs) = do 
  ⟨ t , cs0 ⟩ ← read-termoid false (♭ cs)
  ⟨ ts , cs1 ⟩ ← read-termoid true cs0 
  pass ⟨ cons t ts , cs1 ⟩ 
read-termoid false ('#' ∷* cs) = do 
  ⟨ k , cs0 ⟩ ← read-nat (♭ cs)
  pass ⟨ var k , cs0 ⟩ 
read-termoid false ('$' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-ftr (♭ cs)
  ⟨ ts , cs1 ⟩ ← read-termoid true cs0 
  pass ⟨ fun f ts , cs1 ⟩ 
read-termoid _ _ = fail 

read-term : Costring → IOF (Term × Costring)
read-term = read-termoid false

read-terms : Costring → IOF (Terms × Costring)
read-terms = read-termoid true

-- read-list : {A : Set} → (Costring → Maybe (A × Costring)) → Costring → Maybe (List A × Costring)
-- read-list r ('.' ∷* _) = pass []
-- read-list r (',' ∷* cs) = do 
--   ⟨ x , cs0 ⟩ ← r (♭ cs)
--   ⟨ xs , cs1 ⟩ ← read-list r cs0
--   pass ⟨ x ∷ xs , cs1 ⟩ 

{-# NON_TERMINATING #-}
read-form : Costring → IOF (Form × Costring)
read-form ('T' ∷* cs) = pass ⟨ cst true , ♭ cs ⟩  
read-form ('F' ∷* cs) = pass ⟨ cst false , ♭ cs ⟩  
read-form ('$' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-ftr (♭ cs)
  ⟨ ts , cs1 ⟩ ← read-terms cs0
  pass ⟨ rel f ts , cs1 ⟩ 
read-form ('~' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-form (♭ cs)
  pass ⟨ not f , cs0 ⟩ 
read-form ('!' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-form (♭ cs)
  pass ⟨ qtf false f , cs0 ⟩ 
read-form ('?' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-form (♭ cs)
  pass ⟨ qtf true f , cs0 ⟩ 
read-form ('|' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-form (♭ cs)
  ⟨ g , cs1 ⟩ ← read-form cs0
  pass ⟨ bct or f g , cs1 ⟩ 
read-form ('&' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-form (♭ cs)
  ⟨ g , cs1 ⟩ ← read-form cs0
  pass ⟨ bct and f g , cs1 ⟩ 
read-form ('>' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-form (♭ cs)
  ⟨ g , cs1 ⟩ ← read-form cs0
  pass ⟨ bct imp f g , cs1 ⟩ 
read-form ('=' ∷* cs) = do 
  ⟨ f , cs0 ⟩ ← read-form (♭ cs)
  ⟨ g , cs1 ⟩ ← read-form cs0
  pass ⟨ bct iff f g , cs1 ⟩ 
read-form _ = fail

read-bool : Costring → IOF (Bool × Costring)
read-bool ('T' ∷* cs) = pass ⟨ true , ♭ cs ⟩
read-bool ('F' ∷* cs) = pass ⟨ false , ♭ cs ⟩
read-bool _ = fail

read-af : Costring → IOF ((Chars × Form) × Costring)
read-af cs0 = do 
  ⟨ n , cs1 ⟩ ← read-chars cs0 []
  ⟨ 'T' , cs2 ⟩ ← read-char cs1
    where _ → (put-str-ln "Error : non-axiom in problem" >> fail)
  ⟨ f , cs3 ⟩ ← read-form cs2 
  ⟨ '0' , cs4 ⟩ ← read-char cs3
    where _ → (put-str-ln "Error : annotation in problem" >> fail)
  pass ⟨ ⟨ n , f ⟩ , cs4 ⟩ 

{-# NON_TERMINATING #-}
read-prob : Costring → Prob → IOF Prob
read-prob ('.' ∷* _) P = pass P
read-prob (',' ∷* cs0) P = do 
  ⟨ ⟨ n , f ⟩ , cs1 ⟩ ← read-af (♭ cs0)
  -- put-str (append-all ("Formula name = " ∷ primStringFromList n ∷ ", Formula = " ∷ pp-form f ∷ "\n" ∷ []))
  read-prob cs1 (update-prob P n f)
read-prob (c ∷* _) _ = put-str "Invalid toplevel character for problem input." >> fail
read-prob [] _ = put-str "Unexpected end of problem input." >> fail

put-str-sharp : String → ∞ (IO Unit)
put-str-sharp s = ♯ (putStr s)

get-args : IOF (List String)
get-args = io-to-iof (lift getArgs)

read-check : IOF Unit 
read-check = do 
  (pn ∷ _) ← get-args
    where [] → put-str-ln "No proof file name provided."
  -- put-str "Using proof file = " 
  -- put-str pn 
  ps ← io-to-iof getContents
  P ← read-prob ps empty-prob 
  cs ← io-to-iof (readFiniteFile pn)
  -- put-str "Using proof = "
  -- put-str cs
  check (primStringToList cs) ⟨ P , ⟨ [] , 0 ⟩ ∷ [] , [] , [] ⟩ 
  put-str-ln "ATTV : Proof verified."