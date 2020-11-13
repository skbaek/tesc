module definitions (D : Set) where

open import Data.Empty
open import Relation.Nullary
open import Data.Unit.Base 
open import Data.Unit.Polymorphic renaming (⊤ to ⊤*)
  renaming (tt to tt*)
open import Data.Bool
  renaming (T to tr)
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

eq-elim' : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p y → p x 
eq-elim' p refl = id

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

Rl : Set  
Rl = List D → Bool

Fn : Set 
Fn = List D → D

const-fn : D → Fn 
const-fn d _ = d

RA : Set 
RA = Ftr → Rl 

FA : Set
FA = Ftr → Fn

VA : Set 
VA = Nat → D

infixr 20 _∧_ 
infixr 20 _∨_ 

_∧_ = _×_

and-lft : {A : Set} → {B : Set} → (A ∧ B) → A
and-lft (h , _) = h

and-rgt : {A : Set} → {B : Set} → (A ∧ B) → B
and-rgt (_ , h) = h

data _∨_ : Set → Set → Set where
  or-lft  : ∀ {A B : Set} → A → A ∨ B
  or-rgt : ∀ {A B : Set} → B → A ∨ B

∨-comm : ∀ {A B} → A ∨ B → B ∨ A
∨-comm (or-lft h) = or-rgt h
∨-comm (or-rgt h) = or-lft h

_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

termoid-val : FA → VA → {b : Bool} → Termoid b → ElemList D b
termoid-val _ V (var k) = V k
termoid-val F V (fun f ts) = F f (termoid-val F V ts)
termoid-val F V nil = []
termoid-val F V (cons t ts) = (termoid-val F V t) ∷ (termoid-val F V ts)

term-val : FA → VA → Term → D
term-val F V t = termoid-val F V t

terms-val : FA → VA → Terms → List D
terms-val F V ts = termoid-val F V ts

↓ : VA → VA
↓ V k = V (suc k)

_/_↦r_ : RA → Ftr → Rl → RA 
(R / f0 ↦r r) f1 = if (f0 =ft f1) then r else R f1

_/_↦f_ : FA → Ftr → Fn → FA 
(F / f0 ↦f f) f1 = if (f0 =ft f1) then f else F f1

_/_↦_ : VA → Nat → D → VA 
(V / k ↦ d) m = tri k (V (pred m)) d (V m) m

is-true : Bool → Set 
is-true true = ⊤ 
is-true false = ⊥ 

_,_,_⊢_ : RA → FA → VA → Form → Set
R , F , V ⊢ (cst b) = tr b 
R , F , V ⊢ (not f) = ¬ (R , F , V ⊢ f)
R , F , V ⊢ (bct or f g) = (R , F , V ⊢ f) ∨ (R , F , V ⊢ g)
R , F , V ⊢ (bct and f g) = (R , F , V ⊢ f) ∧ (R , F , V ⊢ g)
R , F , V ⊢ (bct imp f g) = (R , F , V ⊢ f) → (R , F , V ⊢ g)
R , F , V ⊢ (bct iff f g) = (R , F , V ⊢ f) ↔ (R , F , V ⊢ g)
R , F , V ⊢ (qtf false f) = ∀ (x) → (R , F , (V / 0 ↦ x) ⊢ f)
R , F , V ⊢ (qtf true f) = ∃ (\ x → (R , F , (V / 0 ↦ x) ⊢ f))
R , F , V ⊢ (rel r ts) = tr (R r (terms-val F V ts))

_=>_ : Form → Form → Set 
f => g = ∀ R F V → (R , F , V ⊢ bct imp f g)

standard : RA → Set 
standard R = ∀ d0 d1 → (tr (R (sf ('=' ∷ [])) (d0 ∷ d1 ∷ [])) ↔ (d0 ≡ d1))

-- standard : RA → FA → VA → Set 
-- standard R F V = ∀ t s → 
--   ((R , F , V ⊢ (t =* s)) ↔ (term-val F V t ≡ term-val F V s))
-- 
-- standard-ra

_∈_ : {A : Set} → A → List A → Set 
_∈_ _ [] = ⊥
_∈_ x (y ∷ ys) = (x ≡ y) ∨ (x ∈ ys)

in-prob : Form → Prob → Set
in-prob f P = ∃ (\ n → (n , f) ∈ P)

unsat-prob : Prob → Set
unsat-prob P = ∀ R F V → standard R →
  ∃ (\ f → ((in-prob f P) ∧ (¬ R , F , V ⊢ f)))

sats : RA → FA → VA → Prob → Bch → Set
sats R F V P B = ∀ f → ((in-prob f P) ∨ (f ∈ B)) → (R , F , V ⊢ f)

sat : Prob → Bch → Set
sat P B = ∃ λ R → ∃ λ F → ∃ λ V → (standard R ∧ sats R F V P B)

unsat : Prob → Bch → Set
unsat P B = ∀ R F V → standard R → ∃ (λ f → (((in-prob f P) ∨ (f ∈ B)) ∧ (¬ R , F , V ⊢ f)))

pall : {A : Set} → (A → Set) → List A → Set
pall {A} p l = (x : A) → (x ∈ l) → p x

-- nf-in-termoid : ∀ b → Nat → Termoid b → Set
-- nf-in-termoid false k (var _) = ⊥
-- nf-in-termoid false k (fun f ts) = (f ≡ nf k) ∨ nf-in-termoid true k ts
-- nf-in-termoid true k nil = ⊥
-- nf-in-termoid true k (cons t ts) = nf-in-termoid false k t ∨ nf-in-termoid true k ts
-- 
-- nf-in-term : Nat → Term → Set
-- nf-in-term = nf-in-termoid false
-- 
-- nf-in-terms : Nat → Terms → Set
-- nf-in-terms = nf-in-termoid true
-- 
-- nf-in-form : Nat → Form → Set
-- nf-in-form k (cst _) = ⊥ 
-- nf-in-form k (rel f ts) = (f ≡ nf k) ∨ nf-in-terms k ts
-- nf-in-form k (not f) = nf-in-form k f 
-- nf-in-form k (bct _ f g) = nf-in-form k f ∨ nf-in-form k g
-- nf-in-form k (qtf _ f) = nf-in-form k f 

good-ftr : Nat → Ftr → Set
good-ftr k (nf m) = m < k 
good-ftr _ (sf _) = ⊤ 

good-termoid : ∀ {b} → Nat → Termoid b → Set
good-termoid {false} _ (var _) = ⊤ 
good-termoid {false} k (fun f ts) = good-ftr k f ∧ good-termoid k ts
good-termoid {true} _ nil = ⊤ 
good-termoid {true} k (cons t ts) = good-termoid k t ∧ good-termoid k ts 

good-term : Nat → Term → Set
good-term = good-termoid 

good-terms : Nat → Terms → Set
good-terms = good-termoid 

good-form : Nat → Form → Set
good-form _ (cst _) = ⊤
good-form k (rel r ts) = good-ftr k r ∧ good-terms k ts
good-form k (not f) = good-form k f
good-form k (bct _ f g) = good-form k f ∧ good-form k g
good-form k (qtf _ f) = good-form k f

good-bch : Bch → Set
good-bch B = pall (good-form (length B)) B

good-prob : Prob → Set
good-prob P = ∀ f k → in-prob f P → good-form k f

data mono-fun : Nat → Nat → Form → Set where
  mono-fun-fa : ∀ k m f → mono-fun k (suc m) f → mono-fun k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-fun-eq : ∀ k m f → good-ftr k f → 
    mono-fun k m ((fun f (mono-args-lft m)) =* (fun f (mono-args-rgt m)))

data mono-rel : Nat → Nat → Form → Set where
  mono-rel-fa : ∀ k m f → mono-rel k (suc m) f → mono-rel k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-rel-imp : ∀ k m r → good-ftr k r → 
    mono-rel k m ((rel r (mono-args-lft m)) →* (rel r (mono-args-rgt m)))

vars-lt-termoid : ∀ {b} → Nat → Termoid b → Set
vars-lt-termoid {true} _ nil = ⊤
vars-lt-termoid {true} k (cons t ts) = 
  vars-lt-termoid k t ∧ vars-lt-termoid k ts 
vars-lt-termoid {false} k (var m) = m < k
vars-lt-termoid {false} k (fun _ ts) = vars-lt-termoid k ts

vars-lt-form : Nat → Form → Set
vars-lt-form k (rel _ ts) = vars-lt-termoid k ts 
vars-lt-form k (cst _) = ⊤
vars-lt-form k (not f) = vars-lt-form k f
vars-lt-form k (bct _ f g) = vars-lt-form k f ∧ vars-lt-form k g
vars-lt-form k (qtf _ f) = vars-lt-form (suc k) f 

data choice : Nat → Nat → Form → Set where
  choice-fa : ∀ k m f → choice k (suc m) f → choice k m (∀* f)
  choice-imp-asc : ∀ k m f → good-form k f → vars-lt-form (suc m) f → 
    choice k m ((∃* f) →* (subst-form 0 (skolem-term-asc k m) f))
  choice-imp-desc : ∀ k m f → good-form k f → vars-lt-form (suc m) f → 
    choice k m ((∃* f) →* (subst-form 0 (skolem-term-desc k m) f))

data pred-def : Nat → Nat → Form → Set where
  pred-def-fa : ∀ k m f → pred-def k (suc m) f → pred-def k m (∀* f)
  pred-def-iff-asc : ∀ k m f → good-form k f → vars-lt-form m f →
    pred-def k m ((rel (nf k) (vars-asc m)) ↔* f)  
  pred-def-iff-desc : ∀ k m f → good-form k f → vars-lt-form m f →  
    pred-def k m ((rel (nf k) (vars-desc m)) ↔* f)

data jst : Nat → Form → Set where
  jst-top : ∀ k → jst k (cst true)
  jst-not-bot : ∀ k → jst k (not (cst false))
  jst-refl : ∀ k → jst k refl-axiom
  jst-symm : ∀ k → jst k symm-axiom
  jst-trans : ∀ k → jst k trans-axiom
  jst-fun : ∀ k f → mono-fun k 0 f → jst k f
  jst-rel : ∀ k f → mono-rel k 0 f → jst k f
  jst-choice : ∀ k f → choice k 0 f → jst k f
  jst-pred-def : ∀ k f → pred-def k 0 f → jst k f

--  justified _ (not (cst false)) = true 
--  justified k f = disj ( refl-axiom f ∷ symm-axiom f ∷  trans-axiom f ∷ mono-rel f ∷ mono-fun f ∷ is-choice k 0 f ∷ is-pred-def k 0 f ∷ [] )
