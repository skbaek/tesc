{-# OPTIONS --prop #-} 

module attv where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.String
open import Data.List renaming (or to disj) renaming(and to conj)
open import Data.List.Membership.Setoid using (_∈_) 
-- open import Codata.Musical.Notation
-- open import Codata.Musical.Colist
open import Codata.Musical.Costring 
open import Codata.Musical.Colist 
  renaming (map to map*) 
  renaming ([_] to [_]*) 
  renaming (_∷_ to _∷*_) 
open import Data.Unit.Base renaming (⊤ to Unit)
open import Agda.Builtin.Coinduction
open import Data.Maybe.Base 
  renaming (map to map')
  -- renaming (->>=_ to _>>='-)
open import IO renaming (_>>=_ to _>>>=_)
import IO.Primitive as Prim

postulate
  getArgs : Prim.IO (List String)
  getProgName : Prim.IO String
{-# FOREIGN GHC import qualified System.Environment as Env #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC getArgs = fmap (map Text.pack) Env.getArgs #-}
{-# COMPILE GHC getProgName = fmap Text.pack Env.getProgName #-}

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

_⇔_ : Prop → Prop → Prop 
A ⇔ B = (A → B) ∧ (B → A)

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
holds {A} R F V (bct iff f g) = (holds R F V f) ⇔ (holds R F V g)
holds {A} R F V (qtf false f) = ∀[ x ] holds R F (V ₀↦ x) f
holds {A} R F V (qtf true f) = ∃[ x ] holds R F (V ₀↦ x) f
holds {A} R F V (rel r ts) = is-true (R r (terms-val F V ts)) 

unsat : Prob → Prop₁
unsat T = ∀ A R F V → ∃[ n ] ¬ (holds {A} R F V (T n))

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

-- fchtermlist-to-terms : List Term → Terms 
-- termlist-to-terms [] = nil
-- termlist-to-terms (t ∷ ts) = cons t (termlist-to-terms ts)

drop-head : {A : Set} → List A → Nat → Maybe A 
drop-head [] _ = nothing 
drop-head (a ∷ _) 0 = just a 
drop-head (_ ∷ l) (suc k) = drop-head l k 

-- get-from-ctx : List Form → Nat → Nat → Maybe Form 
-- get-from-ctx C 0 i = nothing
-- get-from-ctx C (suc k) i = 
--   if i < (suc k) then drop-head C (k - i) else nothing

Bch : Set 
Bch = List Form × Nat

par : Nat → Term
par k = fun (nf k) nil

get-from-bch : Bch → Nat → Maybe Form 
get-from-bch ⟨ fs , 0 ⟩ i = nothing
get-from-bch ⟨ fs , suc k ⟩ i = if i < (suc k) then drop-head fs (k - i) else nothing

subst-termoid : {b : Bool} → Nat → Term → Termoid b → Termoid b
subst-termoid k t (var m) = if k < m then var (m - 1) else if k == m then t else (var m)
subst-termoid k t (fun f ts) = fun f (subst-termoid k t ts)
subst-termoid k t nil = nil
subst-termoid k t (cons s ts) = cons (subst-termoid k t s) (subst-termoid k t ts)

subst-term : Nat → Term → Term → Term
subst-term k t s = subst-termoid k t s 
 
subst-terms : Nat → Term → Terms → Terms
subst-terms k t ts = subst-termoid k t ts

subst-form : Nat → Term → Form → Form 
subst-form k t (cst b) = cst b
subst-form k t (not f) = not (subst-form k t f)
subst-form k t (bct b f g) = bct b (subst-form k t f) (subst-form k t g)
subst-form k t (qtf q f) = qtf q (subst-form (k + 1) t f)
subst-form k t (rel f ts) = rel f (subst-terms k t ts)

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
break-b (bct or f g) = just ⟨ f , g ⟩ 
break-b (not (bct and f g)) = just ⟨ not f , not g ⟩ 
break-b (bct imp f g) = just ⟨ not f , g ⟩ 
break-b (not (bct iff f g)) = just ⟨ not (bct imp f g) , not (bct imp g f) ⟩ 
break-b _ = nothing

break-c : Term → Form → Maybe Form
break-c t (qtf fa f) = just (subst-form 0 t f)
break-c t (not (qtf ex f)) = just (not (subst-form 0 t f))
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
chars-to-nat-acc k (c ∷ cs) = do 
  m ← char-to-nat c
  chars-to-nat-acc ((k * 10) + m) cs

chars-to-nat : List Char → Maybe Nat  
chars-to-nat = chars-to-nat-acc 0

_&_ : Bool → Bool → Bool 
_&_ true true = true 
_&_ _ _ = false

_↔_ : Bool → Bool → Bool 
_↔_ true true = true
_↔_ false false = true
_↔_ _ _ = false

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
eq-form (cst b') (cst c') = b' ↔ c'
eq-form (not f) (not g) = eq-form f g
eq-form (bct b1 f1 g1) (bct b2 f2 g2) = eq-bct b1 b2 & (eq-form f1 f2 & eq-form g1 g2)
eq-form (qtf p' f') (qtf q' g') = (p' ↔ q') & (eq-form f' g')
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

transit : State → Maybe State
-- app-a 
transit ⟨ P , B ∷ Bs , bool b' ∷ nat n' ∷ [] , app-a ∷ [] ⟩ = do
  f ← get-from-bch B n' >>= break-a b'
  just ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
-- app-b 
transit ⟨ P , B ∷ Bs , nat n' ∷ [] , app-b ∷ [] ⟩ = do
  ⟨ f , g ⟩ ← get-from-bch B n' >>= break-b 
  just ⟨ P , ext-bch f B ∷ ext-bch g B ∷ Bs , [] , [] ⟩
-- app-c 
transit ⟨ P , B ∷ Bs , term t' ∷ nat n' ∷ [] , app-c ∷ [] ⟩ = do
  f ← get-from-bch B n' >>= break-c t' 
  just ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
-- app-d 
transit ⟨ P , B@(⟨ _ , k ⟩) ∷ Bs , nat n' ∷ [] , app-d ∷ [] ⟩ = do
  f ← get-from-bch B n' >>= break-d k 
  just ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
-- app-n 
transit ⟨ P , B ∷ Bs , nat n' ∷ [] , app-n ∷ [] ⟩ = do
  f ← get-from-bch B n' >>= break-n 
  just ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
-- app-p 
transit ⟨ P , B ∷ Bs , chars cs ∷ [] , app-p ∷ [] ⟩ = 
  just ⟨ P , ext-bch (P cs) B ∷ Bs , [] , [] ⟩ 
-- app-s 
transit ⟨ P , B ∷ Bs , form f ∷ [] , app-s ∷ [] ⟩ = 
  just ⟨ P , ext-bch (not f) B ∷ ext-bch f B ∷ Bs , [] , [] ⟩ 
-- app-t 
transit ⟨ P , B ∷ Bs , form f ∷ [] , app-t ∷ [] ⟩ = 
  just ⟨ P , ext-bch f B ∷ Bs , [] , [] ⟩ 
-- app-x 
transit ⟨ P , B ∷ Bs , nat n' ∷ nat p' ∷ [] , app-x ∷ [] ⟩ = do
  f ← get-from-bch B p'
  g ← get-from-bch B n' 
  if eq-form (not f) g then just ⟨ P , Bs , [] , [] ⟩ else nothing
-- get-nat 
transit ⟨ P , Bs , As , get-nat ∷ Is ⟩ = 
  just ⟨ P , Bs , (chars [] ∷ As) , (acc-chars ∷ mk-nat ∷ Is) ⟩ 
-- get-chars 
transit ⟨ P , Bs , As , get-chars ∷ Is ⟩ = 
  just ⟨ P , Bs , (chars [] ∷ As) , (acc-chars ∷ Is) ⟩ 
-- mk-var 
transit ⟨ P , Bs , nat n' ∷ AS , mk-var ∷ IS ⟩ = 
  just ⟨ P , Bs , term (var n') ∷ AS , IS ⟩ 
-- mk-fun 
transit ⟨ P , Bs , terms ts ∷ ftr f ∷ AS , mk-fun ∷ IS ⟩ = 
  just ⟨ P , Bs , term (fun f ts) ∷ AS , IS ⟩ 
-- mk-rel 
transit ⟨ P , Bs , terms ts ∷ ftr f ∷ AS , mk-rel ∷ IS ⟩ = 
  just ⟨ P , Bs , form (rel f ts) ∷ AS , IS ⟩ 
-- mk-cst 
transit ⟨ P , Bs , bool b' ∷ AS , mk-cst ∷ IS ⟩ = 
  just ⟨ P , Bs , form (cst b') ∷ AS , IS ⟩ 
-- mk-not 
transit ⟨ P , Bs , form f ∷ AS , mk-not ∷ IS ⟩ = 
  just ⟨ P , Bs , form (not f) ∷ AS , IS ⟩ 
-- mk-bct 
transit ⟨ P , Bs , form g' ∷ form f' ∷ bct b' ∷ AS , mk-bct ∷ IS ⟩ = 
  just ⟨ P , Bs , form (bct b' f' g') ∷ AS , IS ⟩ 
-- mk-qtf 
transit ⟨ P , Bs , form f' ∷ bool b' ∷ AS , mk-qtf ∷ IS ⟩ = 
  just ⟨ P , Bs , form (qtf b' f') ∷ AS , IS ⟩ 
-- mk-nat 
transit ⟨ P , Bs , chars cs ∷ AS , mk-nat ∷ IS ⟩ = do
  k' ← chars-to-nat cs 
  just ⟨ P , Bs , nat k' ∷ AS , IS ⟩ 
-- mk-cons 
transit ⟨ P , Bs , terms ts' ∷ term t' ∷ AS , mk-cons ∷ IS ⟩ = 
  just ⟨ P , Bs , terms (cons t' ts') ∷ AS , IS ⟩
-- mk-ftr 
transit ⟨ P , Bs , nat n' ∷ AS , mk-nf ∷ IS ⟩ = 
  just ⟨ P , Bs , ftr (nf n') ∷ AS , IS ⟩
transit ⟨ P , Bs , chars cs ∷ AS , mk-sf ∷ IS ⟩ = 
  just ⟨ P , Bs , ftr (sf cs) ∷ AS , IS ⟩
transit S = just S

check : List Char → State → Maybe Unit 

check _ ⟨ _ , [] , _ , _ ⟩ = just tt 

check ('A' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-nat ∷ get-bool ∷ [ app-a ] ⟩ >>= check cs
check ('B' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-nat ∷ [ app-b ] ⟩ >>= check cs
check ('C' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-nat ∷ get-term ∷ [ app-c ] ⟩ >>= check cs
check ('D' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-nat ∷ [ app-d ] ⟩ >>= check cs
check ('N' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-nat ∷ [ app-n ] ⟩ >>= check cs
check ('P' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-chars ∷ [ app-p ] ⟩ >>= check cs
check ('S' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-nat ∷ [ app-s ] ⟩ >>= check cs
check ('T' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-form ∷ [ app-t ] ⟩ >>= check cs
check ('X' ∷ cs) ⟨ P , Bs , [] , [] ⟩ = transit ⟨ P , Bs , [] , get-nat ∷ get-nat ∷ [ app-x ] ⟩ >>= check cs

check ('T' ∷ cs) ⟨ P , Bs , AS , get-bool ∷ IS ⟩ = transit ⟨ P , Bs , bool true  ∷ AS , IS ⟩ >>= check cs 
check ('F' ∷ cs) ⟨ P , Bs , AS , get-bool ∷ IS ⟩ = transit ⟨ P , Bs , bool false ∷ AS , IS ⟩ >>= check cs 

check ('#' ∷ cs) ⟨ P , Bs , AS , get-term ∷ IS ⟩ = transit ⟨ P , Bs , AS , get-nat ∷ mk-var ∷ IS ⟩ >>= check cs 
check ('$' ∷ cs) ⟨ P , Bs , AS , get-term ∷ IS ⟩ = transit ⟨ P , Bs , AS , get-ftr ∷ get-terms ∷ mk-fun ∷ IS ⟩ >>= check cs 

check (',' ∷ cs) ⟨ P , Bs , AS , get-terms ∷ IS ⟩ = transit ⟨ P , Bs , AS , get-term ∷ get-terms ∷ mk-cons ∷ IS ⟩ >>= check cs 
check ('.' ∷ cs) ⟨ P , Bs , AS , get-terms ∷ IS ⟩ = transit ⟨ P , Bs , terms nil ∷ AS , IS ⟩ >>= check cs 

check ('#' ∷ cs) ⟨ P , Bs , AS , get-ftr ∷ IS ⟩ = transit ⟨ P , Bs , AS , get-nat ∷ mk-nf ∷ IS ⟩ >>= check cs 
check ('"' ∷ cs) ⟨ P , Bs , AS , get-ftr ∷ IS ⟩ = transit ⟨ P , Bs , AS , get-chars ∷ mk-sf ∷ IS ⟩ >>= check cs 

check ('$' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , AS , get-ftr ∷ get-terms ∷ mk-rel ∷ IS ⟩ >>= check cs 
check ('~' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , AS , get-form ∷ mk-not ∷ IS ⟩ >>= check cs 
check ('!' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , bool false ∷ AS , get-form ∷ mk-qtf ∷ IS ⟩ >>= check cs 
check ('?' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , bool true  ∷ AS , get-form ∷ mk-qtf ∷ IS ⟩ >>= check cs 
check ('|' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , bct or  ∷ AS , get-form ∷ get-form ∷ mk-bct ∷ IS ⟩ >>= check cs 
check ('&' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , bct and ∷ AS , get-form ∷ get-form ∷ mk-bct ∷ IS ⟩ >>= check cs 
check ('>' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , bct imp ∷ AS , get-form ∷ get-form ∷ mk-bct ∷ IS ⟩ >>= check cs 
check ('=' ∷ cs) ⟨ P , Bs , AS , get-form ∷ IS ⟩ = transit ⟨ P , Bs , bct iff ∷ AS , get-form ∷ get-form ∷ mk-bct ∷ IS ⟩ >>= check cs 

check ('%' ∷ cs0) ⟨ P , Bs , chars cs1 ∷ AS , acc-chars ∷ IS ⟩ = transit ⟨ P , Bs , chars (reverse cs1) ∷ AS , IS ⟩ >>= check cs0
check (c0 ∷ cs0) ⟨ P , Bs , chars cs1 ∷ AS , acc-chars ∷ IS ⟩  = transit ⟨ P , Bs , chars (c0 ∷ cs1) ∷ AS , acc-chars ∷ IS ⟩ >>= check cs0

check _ _ = nothing


{-
data Chars : (i : Size) → Set where 
  []*  : {i : Size} → Chars i
  _∷*_ : {i : Size} → {j : Size< i} → Char → Chars j → Chars i 

Read : {i j : Size} → Set → Set
Read {i} {j} A = Chars i → Maybe (A × Chars j)

_>>=_ : {A B : Set} → Read A → (A → Read B) → Read B 
_>>=_ {A} {B} f g s0 with f s0
... | just ⟨ a0 , s1 ⟩ = g a0 s1
... | _ = nothing
_>>_ : {A B : Set} → Read A → Read B → Read B
_>>_ {A} {B} f g s0 with f s0
... | just (⟨ _ , s1 ⟩) = g s1
... | _ = nothing  
return : {A : Set} → A → Read A 
return a0 s0 = just ⟨ a0 , s0 ⟩  
fail : {A : Set} → Read A 
fail _ = nothing

return-maybe : {A : Set} → Maybe A → Read A 
return-maybe nothing s0 = nothing
return-maybe (just a0) s0 = just ⟨ a0 , s0 ⟩  

get-char : {i : Size} {j : Size< i} → Read {i} {j} Char 
get-char []* = nothing  
get-char {i} {j}(-∷*_ {i} {j} c0 cs) = just ⟨ c0 , {! cs !} ⟩ -- just ⟨ c0 , cs ⟩   

get-nat : Read Nat 
get-nat = {!   !}

get-bool : Read Bool 
get-bool = {!   !}



check : Prob → List Bch → Read Unit 
check P [] = return tt
check P Bs cs with get-char cs
... | nothing = nothing
... | just ⟨ _ , cs' ⟩ = check P Bs cs'
-- check P Bs = do
--   c ← get-char
--   check-char P Bs c 
--   where  
--   check-char : Prob → List Bch → Char → Read Unit 
--   check-char P (⟨ fs , k ⟩ ∷ Bs) 'A' = do
--     -- i ← get-nat 
--     -- b ← get-bool 
--     f ← return-maybe (get-from-bch ⟨ fs , k ⟩ 0)
--     g ← return-maybe (break-a true f) 
--     check P ( ⟨ (g ∷ fs) , (suc k) ⟩ ∷ Bs ) 

-- check-char : Prob → List Form → Nat → Char → Read Unit 
-- check-char P C k 'A' = do 
--   n ← get-nat 
--   d ← get-dir 
--   f ← get-prem n
--   g ← return break-a b f 
--   check P (g ∷ C) (suc k)
-- check-char _ _ _ _ = nothing
-}

update-prob : Prob → Chars → Form → Prob 
update-prob P n f m = if eq-chars n m then f else P m 

empty-prob : Prob 
empty-prob _ = cst true

{-# NON_TERMINATING #-}
read-chars : Costring → Chars → Maybe (Chars × Costring)
read-chars ('%' ∷* s*) cs = just ⟨ reverse cs , ♭ s* ⟩
read-chars (c ∷* s*) cs = read-chars (♭ s*) (c ∷ cs)
read-chars _ _ = nothing

read-form : Costring → Maybe (Form × Costring)
read-form _ = nothing

{-# NON_TERMINATING #-}
read-prob : Costring → Prob → Maybe Prob
read-prob ('.' ∷* _) P = just P 
read-prob (',' ∷* cs0) P = do 
  ⟨ n , cs1 ⟩ ← read-chars (♭ cs0) []
  ⟨ f , cs2 ⟩ ← read-form cs1 
  read-prob cs2 (update-prob P n f)
read-prob _ _ = nothing

foo : Costring → ∞ (IO Unit)
foo s = ♯ (putStr∞ s)

put-str-sharp : String → ∞ (IO Unit)
put-str-sharp s = ♯ (putStr s)

bar : IO Costring 
bar = getContents

quz : IO Unit  
quz = (♯ bar) >>>= foo

get-args : IO (List String)
get-args = lift getArgs

get-head : {A : Set} → List A → IO (Maybe A)
get-head [] = return nothing
get-head (x ∷ _) = return (just x)

get-head_arg : IO (Maybe String)
get-head_arg = (♯ get-args) >>>= (\ x → ♯ (get-head x))

read-check : IO Unit 
read-check = 
  (♯ (lift getArgs)) >>>= 
  λ { []      → ♯ (putStr "Error : no proof file name provided.")
    ; (pn ∷ _) → ♯ (♯ getContents >>>= \ ps → ♯ {!   !} )
    }

main : Prim.IO Unit 
main = run read-check