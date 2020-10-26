module definitions (D : Set) where

open import Data.Empty
open import Relation.Nullary
open import Data.Unit.Base 
open import Data.Unit.Polymorphic renaming (⊤ to ⊤*)
  renaming (tt to tt*)
open import Data.Bool
  renaming (not to bnot)
  renaming (_<_ to _<b_)
  renaming (_∧_ to _&&_)
  renaming (_∨_ to _||_)
open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
  renaming (_==_ to _=n_)
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Data.List renaming (or to disj) renaming(and to conj)
open import Data.Maybe
  renaming (_>>=_ to _?>=_)
  renaming (is-just to is-just-bool)
open import Data.Product
open import basic 
open import verify 

id : ∀ {l} {A : Set l} → A → A 
id x = x

eq-elim : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p x → p y 
eq-elim p refl = id

eq-elim-2 : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} (p : A → B → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → p a0 b0 → p a1 b1 
eq-elim-2 p refl refl = id

eq-trans : ∀ {A : Set} {x : A} (y : A) {z : A} → x ≡ y → y ≡ z → x ≡ z
eq-trans _ refl refl = refl

eq-symm : ∀ {A : Set} {x : A} {y : A} → x ≡ y → y ≡ x
eq-symm refl = refl

data _<_ : Nat → Nat → Set where
  0< : ∀ k → 0 < (suc k)
  suc< : ∀ k m → k < m → suc k < suc m

_>_ : Nat → Nat → Set 
k > m = m < k

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

rl : Set  
rl = List D → Bool

fn : Set 
fn = List D → D

Rls : Set 
Rls = Ftr → rl  

Fns : Set
Fns = Ftr → fn

Vas : Set 
Vas = Nat → D

_∧_ = _×_

and-left : {A : Set} → {B : Set} → (A ∧ B) → A
and-left (h , _) = h

and-right : {A : Set} → {B : Set} → (A ∧ B) → B
and-right (_ , h) = h

data _∨_ : Set → Set → Set where
  or-left  : ∀ {A B : Set} → A → A ∨ B
  or-right : ∀ {A B : Set} → B → A ∨ B

∨-comm : ∀ {A B} → A ∨ B → B ∨ A
∨-comm (or-left h) = or-right h
∨-comm (or-right h) = or-left h

_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

termoid-val : Fns → Vas → {b : Bool} → Termoid b → ElemList D b
termoid-val _ V (var k) = V k
termoid-val F V (fun f ts) = F f (termoid-val F V ts)
termoid-val F V nil = []
termoid-val F V (cons t ts) = (termoid-val F V t) ∷ (termoid-val F V ts)

term-val : Fns → Vas → Term → D
term-val F V t = termoid-val F V t

terms-val : Fns → Vas → Terms → List D
terms-val F V ts = termoid-val F V ts

↓ : Vas → Vas
↓ V k = V (suc k)

_/_↦_ : Vas → Nat → D → Vas 
(V / k ↦ d) m = tri k (V (pred m)) d (V m) m

is-true : Bool → Set 
is-true true = ⊤ 
is-true false = ⊥ 

_,_,_⊢_ : Rls → Fns → Vas → Form → Set
R , F , V ⊢ (cst b) = b ≡ true 
R , F , V ⊢ (not f) = ¬ (R , F , V ⊢ f)
R , F , V ⊢ (bct or f g) = (R , F , V ⊢ f) ∨ (R , F , V ⊢ g)
R , F , V ⊢ (bct and f g) = (R , F , V ⊢ f) ∧ (R , F , V ⊢ g)
R , F , V ⊢ (bct imp f g) = (R , F , V ⊢ f) → (R , F , V ⊢ g)
R , F , V ⊢ (bct iff f g) = (R , F , V ⊢ f) ↔ (R , F , V ⊢ g)
R , F , V ⊢ (qtf false f) = ∀ (x) → (R , F , (V / 0 ↦ x) ⊢ f)
R , F , V ⊢ (qtf true f) = ∃ (\ x → (R , F , (V / 0 ↦ x) ⊢ f))
R , F , V ⊢ (rel r ts) = (R r (terms-val F V ts)) ≡ true

_=>_ : Form → Form → Set 
f => g = ∀ R F V → (R , F , V ⊢ bct imp f g)

_=*_ : Term → Term → Form
t =* s = rel (sf ('=' ∷ [])) (cons t (cons s nil))

standard : Rls → Fns → Vas → Set 
standard R F V = ∀ t s → 
  ((R , F , V ⊢ (t =* s)) ↔ (term-val F V t ≡ term-val F V s))

_∈_ : {A : Set} → A → List A → Set 
_∈_ _ [] = ⊥
_∈_ x (y ∷ ys) = (x ≡ y) ∨ (x ∈ ys)

in-prob : Form → Prob → Set
in-prob f P = ∃ (\ n → (n , f) ∈ P)

unsat-prob : Prob → Set
unsat-prob P = ∀ R F V → standard R F V →
  ∃ (\ f → ((in-prob f P) ∧ (¬ R , F , V ⊢ f)))

unsat : Prob → Bch → Set
unsat P B = ∀ R F V → standard R F V → ∃ (\ f → (((in-prob f P) ∨ (f ∈ B)) ∧ (¬ R , F , V ⊢ f)))

pall : {A : Set} → (A → Set) → List A → Set
pall {A} p l = (x : A) → (x ∈ l) → p x

nf-in-termoid : ∀ b → Nat → Termoid b → Set
nf-in-termoid false k (var _) = ⊥
nf-in-termoid false k (fun f ts) = (f ≡ nf k) ∨ nf-in-termoid true k ts
nf-in-termoid true k nil = ⊥
nf-in-termoid true k (cons t ts) = nf-in-termoid false k t ∨ nf-in-termoid true k ts

nf-in-term : Nat → Term → Set
nf-in-term = nf-in-termoid false

nf-in-terms : Nat → Terms → Set
nf-in-terms = nf-in-termoid true

nf-in-form : Nat → Form → Set
nf-in-form k (cst _) = ⊥ 
nf-in-form k (rel f ts) = (f ≡ nf k) ∨ nf-in-terms k ts
nf-in-form k (not f) = nf-in-form k f 
nf-in-form k (bct _ f g) = nf-in-form k f ∨ nf-in-form k g
nf-in-form k (qtf _ f) = nf-in-form k f 

good-termoid : ∀ b → Nat → Termoid b → Set
good-termoid b k t = ∀ m → nf-in-termoid b m t → m < k

good-term : Nat → Term → Set
good-term = good-termoid false

good-terms : Nat → Terms → Set
good-terms = good-termoid true

good-form : Nat → Form → Set
good-form k f = ∀ m → nf-in-form m f → m < k

good-bch : Bch → Set
good-bch B = pall (good-form (length B)) B