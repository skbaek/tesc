module correct (D : Set) where

open import Data.Empty
open import Relation.Nullary
open import Data.Unit.Base 
open import Data.Unit.Polymorphic renaming (⊤ to ⊤*)
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
 
postulate LEM : (A : Set) → Dec A
postulate FX : ∀ {A B : Set} (f g : A → B) (h : ∀ a → f a ≡ f a) → f ≡ g

data _<_ : Nat → Nat → Set where
  0< : ∀ k → 0 < (suc k)
  suc< : ∀ k m → k < m → suc k < suc m

_>_ : Nat → Nat → Set 
k > m = m < k

<-to-<-suc : ∀ k m → k < m → k < suc m
-- <-to-<-suc _ 0 ()
-- <-to-<-suc 0 _ _ = refl
-- <-to-<-suc (suc k) (suc m) h = <-to-<-suc k m h
<-to-<-suc 0 m _ = 0< _
<-to-<-suc (suc k) 0 ()
<-to-<-suc (suc k) (suc m) (suc< k m h) = suc< k _ (<-to-<-suc k m h)

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
(V / k ↦ d) m = tri k (V m) d (V (pred m)) m
-- (V / 0 ↦ d) 0  = d
-- (V / 0 ↦ d) (suc m) = V m
-- (V / (suc k) ↦ d) 0 = V 0
-- (V / (suc k) ↦ d) (suc m) = ((↓ V) / k ↦ d) m

-- _₀↦_ : Vas → D → Vas 
-- _₀↦_ V a 0 = a
-- _₀↦_ V a (suc k) = V k

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

or-elim : ∀ {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
or-elim (or-left x) f g = f x
or-elim (or-right x) f g = g x

or-elim' : ∀ {A B C : Set} → (A → C) → (B → C) → (A ∨ B) → C
or-elim' ha hb hab = or-elim hab ha hb

unsat : Prob → Bch → Set
unsat P B = ∀ R F V → standard R F V → ∃ (\ f → (((in-prob f P) ∨ (f ∈ B)) ∧ (¬ R , F , V ⊢ f)))

exist-elim : ∀ {A B : Set} {P : A → Set} → (∃ P) → (∀ (x : A) → P x → B) → B
exist-elim (a , h0) h1 = h1 a h0

id : ∀ {l} {A : Set l} → A → A 
id x = x

not-elim : ∀ {A B} → A → (¬ A) → B
not-elim h0 h1 = ⊥-elim (h1 h0)

pall : {A : Set} → (A → Set) → List A → Set
pall {A} p l = (x : A) → (x ∈ l) → p x

pall-nil : {A : Set} {p : A → Set} → pall p []
pall-nil {A} {p} x = ⊥-elim

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

good-form : Nat → Form → Set
good-form k f = ∀ m → nf-in-form m f → m < k

good-bch : Bch → Set
good-bch B = pall (good-form (length B)) B

eq-elim : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p x → p y 
eq-elim p refl = id

eq-elim-2 : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} (p : A → B → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → p a0 b0 → p a1 b1 
eq-elim-2 p refl refl = id

eq-trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
eq-trans refl refl = refl

eq-symm : ∀ {A : Set} {x : A} {y : A} → x ≡ y → y ≡ x
eq-symm refl = refl


ite-elim-eq : ∀ {A : Set} {x y : A} (b : Bool) → 
  (P : A → Set) → (b ≡ true → P x) → (b ≡ false → P y) → P (if b then x else y)
ite-elim-eq false P hx hy = hy refl
ite-elim-eq true  P hx hy = hx refl

ite-elim : ∀ {A : Set} {x : A} {y : A} (b : Bool) → 
  (P : A → Set) → P x → P y → P (if b then x else y)
ite-elim false P hx hy = hy
ite-elim true  P hx hy = hx

ite-true-eq : ∀ {A : Set} {x y : A} {b : Bool} → 
  b ≡ true → (if b then x else y) ≡ x
ite-true-eq refl = refl

ite-false-eq : ∀ {A : Set} {x y : A} {b : Bool} → 
  b ≡ false → (if b then x else y) ≡ y
ite-false-eq refl = refl

cong :
  {A : Set}
  {B : Set}
  (f : A → B)
  {x y : A}
  (p : x ≡ y)
  → -----------
  f x ≡ f y
cong _ refl = refl

cong2 :
  {A B C : Set}
  (f : A → B → C)
  {x y : A}
  {z w : B}
  (p : x ≡ y)
  (q : z ≡ w)
  → -----------
  f x z ≡ f y w
cong2 _ refl refl = refl

elim-bool-absurd : ∀ {b : Bool} {A : Set} → b ≡ true → b ≡ false → A 
elim-bool-absurd refl ()

trichotomy : ∀ k m → ((k < m) ∨ ((k ≡ m) ∨ (k > m)))
trichotomy 0 0 = or-right (or-left refl)
trichotomy 0 (suc m) = or-left (0< _)
trichotomy (suc k) 0 = or-right (or-right (0< _))
trichotomy (suc k) (suc m) = 
  or-elim (trichotomy k m) 
    (\ h0 → or-left (suc< _ _ h0)) 
    \ h0 → or-elim h0 
      (\ h1 → or-right (or-left _)) 
      \ h1 → or-right (or-right (suc< _ _ h1))

<-to-<n : ∀ k m → k < m → ((k <n m) ≡ true)  
<-to-<n 0 (suc m) (0< m) = refl
<-to-<n (suc k) (suc m) (suc< k m h) = <-to-<n k m h

<n-to-< : ∀ k m → ((k <n m) ≡ true) → k < m
<n-to-< _ 0  ()
<n-to-< 0 (suc m) _ = 0< m 
<n-to-< (suc k) (suc m) h = suc< k m (<n-to-< k m h)

≡-to-=n : ∀ k m → k ≡ m → ((k =n m) ≡ true)  
≡-to-=n 0 0 refl = refl
≡-to-=n (suc k) (suc m) h = ≡-to-=n k m (suc-inj h) 

=n-to-≡ : ∀ k m → ((k =n m) ≡ true) → k ≡ m
=n-to-≡ 0 0 _ = refl
=n-to-≡ 0 (suc m) ()
=n-to-≡ (suc k) 0 ()
=n-to-≡ (suc k) (suc m) h = cong suc (=n-to-≡ k m h)
  
tri-eq-lt : ∀ {A : Set} {a b c : A} (k m : Nat) → (k < m) → (tri k a b c m) ≡ a 
tri-eq-lt = {!   !}
tri-eq-eq : ∀ {A : Set} {a b c : A} (k m : Nat) → (k ≡ m) → (tri k a b c m) ≡ b 
tri-eq-eq = {!   !}
tri-eq-gt : ∀ {A : Set} {a b c : A} (k m : Nat) → (k > m) → (tri k a b c m) ≡ c 
tri-eq-gt = {!   !}

tri-elim : ∀ {A : Set} {a b c : A} (k m : Nat) → (P : A → Set) →
  (k < m → P a) → (k ≡ m → P b) → (k > m → P c) → P (tri k a b c m)
tri-elim k m P hl he hg = 
  ite-elim-eq (k <n m) P 
    (\ h0 → hl  (<n-to-< _ _ h0)) 
    \ h0 → ite-elim-eq (k =n m) P 
      (\ h1 → he (=n-to-≡ _ _ h1)) 
      \ h1 → (hg ( or-elim (trichotomy k m) 
        (\ h2 → elim-bool-absurd (<-to-<n _ _ h2) h0) 
        (or-elim' (\h3 → elim-bool-absurd (≡-to-=n _ _ h3) h1) id) )) 

mp : {A B : Set} → A → (A → B) → B
mp h0 h1 = h1 h0 

modus-tollens : ∀ {A : Set} {B : Set} → (A → B) → ¬ B → ¬ A  
modus-tollens h0 h1 h2 = ⊥-elim (h1 (h0 h2))

holds-or-nothing  : ∀ {A : Set} → (P : A → Set) → Maybe A → Set
holds-or-nothing P nothing = ⊤* 
holds-or-nothing P (just x) = P x 

just-and-holds  : ∀ {A : Set} → (P : A → Set) → Maybe A → Set
just-and-holds P m = ∃ (\ a → ((m ≡ (just a)) ∧ P a))

maybe-elim : ∀ {A : Set} → (P : Maybe A → Set) → 
  (P nothing) → ((x : A) → P (just x)) → (m : Maybe A) → P m 
maybe-elim P hn hj nothing = hn
maybe-elim P hn hj (just x) = hj x

maybe-elim-conc : ∀ {A : Set} {m : Maybe A} → (P : Maybe A → Set) → (Q : Set) → 
  (P nothing → Q) → ((x : A) → P (just x) → Q) → P m → Q 
maybe-elim-conc P Q hn hj hm = maybe-elim (\ x → (P x → Q)) hn hj _ hm

maybe-absurd : ∀ {A B : Set} {x : A} → nothing ≡ (just x) → B 
maybe-absurd ()

of-bind-eq-just : ∀ {A B : Set} → 
  (f : Maybe A) → (g : A → Maybe B) → (b : B) → 
  (f ?>= g) ≡ just b → ∃ (\ a → (f ≡ just a) ∧ (g a ≡ just b))
of-bind-eq-just nothing g b = maybe-absurd
of-bind-eq-just (just a) g b = \ h → (a , (refl , h))


use-lem : ∀ (A : Set) {B : Set} → (A → B) → ((¬ A) → B) → B
use-lem A h0 h1 with LEM A 
... | (yes h2) = h0 h2
... | (no h2)  = h1 h2

not-or-left : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ A 
not-or-left h0 h1 = h0 (or-left h1)  

not-or-right : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ B 
not-or-right h0 h1 = h0 (or-right h1)  

not-imp-left : ∀ {A B : Set} → ¬ (A → B) → A 
not-imp-left {A} {B} h0 = use-lem  A id \ h1 → ⊥-elim (h0 \ h2 → ⊥-elim (h1 h2))

not-imp-right : ∀ {A B : Set} → ¬ (A → B) → ¬ B 
not-imp-right {A} {B} h0 h1 = ⊥-elim (h0 \ h2 → h1)

imp-to-not-or :  ∀ {A B} → (A → B) → ((¬ A) ∨ B)
imp-to-not-or {A} {B} h0 = use-lem A (\ h1 → or-right (h0 h1)) or-left 

not-and-to-not-or-not :  ∀ {A B} → ¬ (A ∧ B) → ((¬ A) ∨ (¬ B))
not-and-to-not-or-not {A} {B} h0 = use-lem A 
  (\ h1 → use-lem B (\ h2 → ⊥-elim (h0 (h1 , h2))) or-right) 
  or-left

prod-inj-left : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} → 
  (a0 , b0) ≡ (a1 , b1) → a0 ≡ a1
prod-inj-left refl = refl

prod-inj-right : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} → 
  (a0 , b0) ≡ (a1 , b1) → b0 ≡ b1
prod-inj-right refl = refl


implies-c : ∀ t f g → break-c t f ≡ just g → f => g
implies-c = {!   !}

implies-b : ∀ f g h → break-b f ≡ just (g , h) → f => (bct or g h)
implies-b (bct or f0 f1) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (bct or f0 f1 => bct or x y)) 
    (prod-inj-left h1) (prod-inj-right h1) \ _ _ _ → id
implies-b (bct imp f0 f1) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (bct imp f0 f1 => bct or x y)) 
    (prod-inj-left h1) (prod-inj-right h1) \ R F V → imp-to-not-or
implies-b (not (bct and f0 f1)) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (not (bct and f0 f1) => bct or x y)) 
    (prod-inj-left h1) (prod-inj-right h1) \ R F V → not-and-to-not-or-not
implies-b (not (bct iff f0 f1)) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (not (bct iff f0 f1) => bct or x y)) 
    (prod-inj-left h1) (prod-inj-right h1) \ R F V → not-and-to-not-or-not

implies-a : ∀ b f g → break-a b f ≡ just g → f => g
implies-a true  (bct and f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-left h1) 
implies-a false (bct and f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-right h1) 
implies-a true  (bct iff f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-left h1) 
implies-a false (bct iff f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-right h1) 
implies-a true  (not (bct or f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-or-left h1) 
implies-a false (not (bct or f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-or-right h1) 
implies-a true  (not (bct imp f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-imp-left h1) 
implies-a false (not (bct imp f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-imp-right h1) 

not-iff-not : ∀ {A B} → (A ↔ B) → ((¬ A) ↔ (¬ B))
not-iff-not h0 = 
  ( (\ ha hb → ⊥-elim (ha (and-right h0 hb))) , 
    (\ hb ha → ⊥-elim (hb (and-left h0 ha))) ) 

or-iff-or : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∨ B0) ↔ (A1 ∨ B1))
or-iff-or ha hb = 
  (\ h0 → or-elim h0 
    (\ h1 → (or-left (and-left ha h1))) 
    (\ h1 → (or-right (and-left hb h1)))) , 
  (\ h0 → or-elim h0 
    (\ h1 → (or-left (and-right ha h1))) 
    (\ h1 → (or-right (and-right hb h1)))) 
    

and-iff-and : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∧ B0) ↔ (A1 ∧ B1))
and-iff-and ha hb = {!   !}

imp-iff-imp : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 → B0) ↔ (A1 → B1))
imp-iff-imp ha hb = {!   !}

iff-iff-iff : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ↔ B0) ↔ (A1 ↔ B1))
iff-iff-iff ha hb = {!   !}

fa-iff-fa : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∀ a → P a) ↔ (∀ a → Q a))
fa-iff-fa h0 = ((\ h1 a → and-left (h0 a) (h1 a)) , (\h1 a → and-right (h0 a) (h1 a)))

ex-iff-ex : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∃ P) ↔ (∃ Q))
ex-iff-ex h0 = {!   !}

term-val-incr : ∀ F V t d → term-val F (V / 0 ↦ d) (incr-var-term t) ≡ term-val F V t 
term-val-incr F V t d = {!   !}

update-update : ∀ V k d e → ((V / 0 ↦ e ) / (suc k) ↦ d) ≡ ((V / k ↦ d) / 0 ↦ e) 
update-update V k d e = FX _ _ \ { 0 → refl ; (suc m) → refl }

-- vas-gt : ∀ V k d m → k < (suc m) → (V / k ↦ d) (suc m) ≡ V m 
-- vas-gt V k d 0 ()
-- vas-gt V 0 d m h0 = refl
-- vas-gt V (suc k) d (suc m) = \ h0 → eq-trans (vas-gt (↓ V) k d m h0) refl

-- update-eq : ∀ V k d → (V / k ↦ d) k ≡ d
-- update-eq V 0 d = refl 
-- update-eq V (suc k) d = update-eq _ k d 
-- 
-- var-val-subst : ∀ F V a k t m → (V / (a + k) ↦ 
--   term-val F V t) (a + m) ≡ termoid-val F V (subst-var a k t m)
-- var-val-subst F V a 0 t 0 = update-eq V (a + zero) _ 
-- var-val-subst F V a (suc k) t 0 = {!   !}

iff-self : ∀ {A} → (A ↔ A)
iff-self = (id , id)

eq-to-iff : ∀ {A : Set} (P : A → Set) (x y : A) → x ≡ y → ((P x) ↔ (P y))
eq-to-iff P x y refl = iff-self  

termoid-val-subst : ∀ (F : Fns) (V : Vas) (k : Nat) (b : Bool) (s : Term) (t : Termoid b) → 
  (termoid-val F (V / k ↦ term-val F V s) t) ≡ (termoid-val F V (subst-termoid k s t))
termoid-val-subst F V k true s nil = refl
termoid-val-subst F V k true s (cons t ts) = 
  cong2 _∷_ (termoid-val-subst F V k false s t) 
    (termoid-val-subst F V k true s ts)
termoid-val-subst F V k false s (var m) = 
  tri-elim k m 
    (λ x → (V / k ↦ term-val F V s) m ≡ termoid-val F V x)
    (\ h0 → eq-trans (tri-eq-lt k m h0) refl) 
    (\ h0 → eq-trans (tri-eq-eq k m h0) refl) 
    (\ h0 → eq-trans (tri-eq-gt k m h0) refl)
termoid-val-subst F V k false s (fun f ts) = 
  cong (F f) (termoid-val-subst F V k true _ ts)

holds-subst : ∀ R F V k t f → 
  ((R , F , (V / k ↦ (term-val F V t)) ⊢ f) ↔ (R , F , V ⊢ subst-form k t f))
holds-subst R F V k t (rel r ts) = 
  eq-to-iff (\ x → (R r x ≡ true)) _ _ (termoid-val-subst F V k true _ ts)
holds-subst R F V k t (cst b) = ( id , id )
holds-subst R F V k t (not f) = not-iff-not (holds-subst _ _ _ k t f)
holds-subst R F V k t (bct or f g) = 
  or-iff-or (holds-subst _ _ _ k t f) (holds-subst _ _ _ k t g) 
holds-subst R F V k t (bct and f g) = 
  and-iff-and (holds-subst _ _ _ k t f) (holds-subst _ _ _ k t g) 
holds-subst R F V k t (bct imp f g) = 
  imp-iff-imp (holds-subst _ _ _ k t f) (holds-subst _ _ _ k t g) 
holds-subst R F V k t (bct iff f g) = 
  iff-iff-iff (holds-subst _ _ _ k t f) (holds-subst _ _ _ k t g) 
holds-subst R F V k t (qtf true f) = ex-iff-ex \ d →  
  eq-elim 
    (\ x → ((R , F , x ⊢ f) ↔ (R , F , V / 0 ↦ d ⊢ subst-form (suc k) (incr-var-term t) f))) 
    (update-update V k (term-val F V t) d) 
    ( eq-elim 
      (\ x → (R , F , (V / 0 ↦ d) / suc k ↦ x ⊢ f) ↔ (R , F , V / 0 ↦ d ⊢ subst-form (suc k) (incr-var-term t) f)) 
      (term-val-incr F V t d) (holds-subst R F _ (suc k) (incr-var-term t) f))
holds-subst R F V k t (qtf false f) = fa-iff-fa \ d → 
  eq-elim 
    (\ x → ((R , F , x ⊢ f) ↔ (R , F , V / 0 ↦ d ⊢ subst-form (suc k) (incr-var-term t) f))) 
    (update-update V k (term-val F V t) d) 
    ( eq-elim 
      (\ x → (R , F , (V / 0 ↦ d) / suc k ↦ x ⊢ f) ↔ (R , F , V / 0 ↦ d ⊢ subst-form (suc k) (incr-var-term t) f)) 
      (term-val-incr F V t d) (holds-subst R F _ (suc k) (incr-var-term t) f))




good-form-suc : ∀ k f → good-form k f → good-form (suc k) f
good-form-suc k f h0 m h1 = <-to-<-suc _ _ (h0 _ h1)

good-bch-cons : ∀ f B → good-form (suc (length B)) f → good-bch B → good-bch (f ∷ B)
good-bch-cons f B h0 h1 g h2 = or-elim h2 
  (\ h3 → eq-elim _ (eq-symm h3) h0) 
  \ h3 k h4 → <-to-<-suc _ _ (h1 _ h3 _ h4)

prsv-implies : ∀ P B f g → f ∈ B → f => g → unsat P (g ∷ B) → unsat P B 
prsv-implies P B f g h0 h1 h2 R F V h3 = 
  exist-elim (h2 R F V h3) ( \ h h4 → let h5 = and-right h4 
    in or-elim (and-left h4) 
      (\ h6 → (h , (or-left h6 , h5))) 
      \ h6 → or-elim h6 
        (\ h7 → (f , (or-right h0 , modus-tollens 
           (\ h8 → eq-elim (\ x → R , F , V ⊢ x) (eq-symm h7) 
             (h1 R F V h8))
          h5) ) ) 
        \ h7 → (h , (or-right h7 , h5)) )

prsv-a : ∀ P B b f g → f ∈ B → (break-a b f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-a P B b f g h0 h1 = prsv-implies P B f g h0 (implies-a _ _ _ h1) 

unsat-or-cons : ∀ P B f g → unsat P (f ∷ B) → unsat P (g ∷ B) → unsat P (bct or f g ∷ B)
unsat-or-cons P B f g hf hg R F V hs = exist-elim (hf R F V hs) \ f' h0 → 
  or-elim (and-left h0) 
    (\ h1 → (f' , (or-left h1 , and-right h0))) 
    ( or-elim' 
      ( \ h2 → exist-elim (hg R F V hs) \ g' h3 → 
        or-elim (and-left h3) 
          (\ h4 → (g' , (or-left h4 , and-right h3))) 
          ( or-elim' 
            ( \ h4 → ( bct or f g , 
              ( or-right (or-left refl), 
                or-elim' 
                  (eq-elim (λ x → ¬ (R , F , V ⊢ x)) h2 (and-right h0)) 
                  (eq-elim (λ x → ¬ (R , F , V ⊢ x)) h4 (and-right h3)) ) ) ) 
            (\ h4 → (g' , (or-right (or-right h4) , and-right h3))) )
      ) 
      (\ h1 → (f' , (or-right (or-right h1) , and-right h0))) )

prsv-b : ∀ P B f g h → f ∈ B → (break-b f ≡ just (g , h)) → 
  unsat P (g ∷ B) → unsat P (h ∷ B) → unsat P B 
prsv-b P B f g h h0 h1 h2 h3 = prsv-implies P B f (bct or g h) 
  h0 (implies-b _ _ _ h1) (unsat-or-cons _ _ _ _ h2 h3)

prsv-c : ∀ P B t f g → f ∈ B → (break-c t f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-c P B t f g h1 h2 h3 = prsv-implies P B f g h1 (implies-c t f g h2) h3
  
-- Good-proofs

prsv-good-b : ∀ f g h k → (break-b f ≡ just (g , h)) → good-form k f → 
  (good-form k g ∧ good-form k h)
prsv-good-b (bct or f0 f1) g h k h0 h1 = 
  ( (eq-elim (good-form k) (prod-inj-left (just-inj h0)) \ m h2 → h1 m (or-left h2)) , 
    (eq-elim (good-form k) (prod-inj-right (just-inj h0)) \ m h2 → h1 m (or-right h2)) )
prsv-good-b (bct imp f0 f1) g h k h0 h1 = 
  ( (eq-elim (good-form k) (prod-inj-left (just-inj h0)) \ m h2 → h1 m (or-left h2)) , 
    (eq-elim (good-form k) (prod-inj-right (just-inj h0)) \ m h2 → h1 m (or-right h2)) )
prsv-good-b (not (bct and f0 f1)) g h k h0 h1 = 
  ( (eq-elim (good-form k) (prod-inj-left (just-inj h0)) \ m h2 → h1 m (or-left h2)) , 
    (eq-elim (good-form k) (prod-inj-right (just-inj h0)) \ m h2 → h1 m (or-right h2)) )
prsv-good-b (not (bct iff f0 f1)) g h k h0 h1 = 
  ( (eq-elim (good-form k) (prod-inj-left (just-inj h0)) h1) , 
    (eq-elim (good-form k) (prod-inj-right (just-inj h0)) \ m h2 → h1 m (∨-comm h2)) )

prsv-good-a : ∀ b f g k → (break-a b f ≡ just g) → good-form k f → good-form k g
prsv-good-a true  (bct and f0 f1) g k h0 h1 = 
  eq-elim (good-form k) (just-inj h0) \ m h2 → h1 m (or-left h2)
prsv-good-a false (bct and f0 f1) g k h0 h1 = 
  eq-elim (good-form k) (just-inj h0) \ m h2 → h1 m (or-right h2)
prsv-good-a true  (bct iff f0 f1) g k h0 h1 = 
  eq-elim (good-form k) (just-inj h0) h1
prsv-good-a false (bct iff f0 f1) g k h0 h1 =
  eq-elim (good-form k) (just-inj h0) \ m h2 → h1 m (∨-comm h2)
prsv-good-a true  (not (bct or f0 f1)) g k h0 h1 = 
  eq-elim (good-form k) (just-inj h0) \ m h2 → h1 m (or-left h2)
prsv-good-a false (not (bct or f0 f1))  g k h0 h1 =
  eq-elim (good-form k) (just-inj h0) \ m h2 → h1 m (or-right h2)
prsv-good-a true  (not (bct imp f0 f1)) g k h0 h1 =
  eq-elim (good-form k) (just-inj h0) \ m h2 → h1 m (or-left h2)
prsv-good-a false (not (bct imp f0 f1)) g k h0 h1 =
  eq-elim (good-form k) (just-inj h0) \ m h2 → h1 m (or-right h2)

good-bch-a : ∀ B b f g → f ∈ B → (break-a b f ≡ just g) → good-bch B → good-bch (g ∷ B)
good-bch-a B b f g h0 h1 h2 = good-bch-cons _ _ 
  (good-form-suc _ g (prsv-good-a _ _ _ _ h1 (h2 f h0))) h2 

good-bch-b : ∀ B f g h → f ∈ B → (break-b f ≡ just (g , h)) → 
  good-bch B → (good-bch (g ∷ B) ∧ good-bch (h ∷ B))
good-bch-b B f g h h0 h1 h2 = 
  ( good-bch-cons _ _ (good-form-suc _ g (and-left  (prsv-good-b _ _ _ _ h1 (h2 f h0)))) h2 , 
    good-bch-cons _ _ (good-form-suc _ h (and-right (prsv-good-b _ _ _ _ h1 (h2 f h0)))) h2 )
  

is-just : ∀  {A : Set} → Maybe A → Set
is-just nothing = ⊥
is-just (just _) = ⊤

from-is-just : ∀ {A} {B} → (f : Read A) → (g : A → Read B) → 
  ∀ cs → is-just ((f >>= g) cs) → 
    ∃ (\ x → ∃ (\ cs' → (f cs ≡ just (x , cs')) ∧ (is-just (g x cs'))))
from-is-just f g cs with f cs 
... | nothing = \ h0 → ⊥-elim h0 
... | (just (x , cs')) = \ h0 → (x , (cs' , (refl , h0)))


use-is-just-bind : ∀ {A B C : Set} → 
  (f : Read A) → (g : A → Read B) → ∀ cs → 
    (∀ a cs' → (f cs ≡ just (a , cs')) → (is-just (g a cs')) → C) → 
      is-just ((f >>= g) cs) → C
use-is-just-bind f g cs h0 h1 = 
  exist-elim (from-is-just f g cs h1) 
    \ a h2 → exist-elim h2 \ cs' h3 → h0 a cs' (and-left h3) (and-right h3)
    
from-obind-eq-just : ∀ {A B : Set} (f : Maybe A) (g : A → Maybe B) (b : B) → 
  (f ?>= g) ≡ just b → ∃ \ a → ((f ≡ just a) ∧ (g a ≡ just b))
from-obind-eq-just nothing _ _  () 
from-obind-eq-just (just a) g b h0 = (a , (refl , h0))

from-lift-read-eq-just : {A : Set} → (f : Maybe A) → (a : A) → (cs0 cs1 : Chars) → 
  ((lift-read f) cs0 ≡ just (a , cs1)) → f ≡ just a
from-lift-read-eq-just nothing _ _ _ ()
from-lift-read-eq-just (just a0) a1 cs0 c1 h0 = cong just (prod-inj-left (just-inj h0))

from-nth-eq-just : ∀ {A : Set} k l (x : A) → nth k l ≡ just x → x ∈ l
from-nth-eq-just 0 (y ∷ _) x = \ h0 → or-left (eq-symm (just-inj h0))
from-nth-eq-just (suc m) (_ ∷ ys) x = \ h0 → or-right (from-nth-eq-just m ys x h0)

from-get-bch-eq-just : ∀ B m f → get-bch B m ≡ just f → f ∈ B
from-get-bch-eq-just B m f h0 =  
  exist-elim 
    (from-obind-eq-just 
      (rev-index (length B) m) 
      (\ n → nth n B) f h0) 
      \ k h1 → from-nth-eq-just k _ _ (and-right h1)

from-lift-read-get-bch : ∀ {A : Set} B m (d : Form → Maybe A) f cs0 cs1 →  
  lift-read (get-bch B m ?>= d) cs0 ≡ just (f , cs1) → 
    ∃ \ g → ((g ∈ B) ∧ (d g ≡ just f))
from-lift-read-get-bch B m d f cs0 cs1 h0 = 
  let h1 : ∃ \ g → ((get-bch B m ≡ just g) ∧ (d g ≡ just f))
      h1 =  from-obind-eq-just _ d f (from-lift-read-eq-just _ f _ _ h0) 
  in exist-elim h1 \ g h2 → 
    (g , (from-get-bch-eq-just _ _ _ (and-left h2) , and-right h2))

correct-aux : ∀ {f g : Read ⊤} P B c0 c1 cs
  (h0 : is-just (f cs) → unsat P B)  
  (h1 : is-just (g cs) → unsat P B)  
  → -------------------------------
  is-just ((if c0 ==c c1 then f else g) cs) → unsat P B 
correct-aux P B c0 c1 cs = 
  ite-elim (c0 ==c c1) (λ (x : Read ⊤) → is-just (x cs) → unsat P B) 

use-is-just-seq : ∀ {A B C : Set} (r : Read A) (s : Read B) (cs) → 
  (∀ a cs' → r cs ≡ just (a , cs') → (is-just (s cs')) → C) → 
  is-just ((r >> s) cs) → C
use-is-just-seq r s cs h0  with (r cs) 
... | nothing = ⊥-elim 
... | just (a , cs') = h0 a cs' refl

use-is-just-pass-if-seq : ∀ {A B : Set} b (r : Read A) cs → 
  ((b ≡ true) → is-just (r cs) → B) → 
  is-just ((pass-if b >> r) cs) → B
use-is-just-pass-if-seq true r cs h0 = h0 refl

eq-just-to-is-just : ∀ {A} (m : Maybe A) (a : A) → m ≡ just a → is-just m 
eq-just-to-is-just nothing _ ()
eq-just-to-is-just (just _) _ _ = tt


use-get-bch : 
  {X : Set} 
  {Y : Set}
  (B : Bch)
  (k : Nat)
  (d : Form → Maybe X)
  (r : X → Read ⊤)
  (cs : Chars)
  (h0 : ∀ f x cs' → (f ∈ B) → (d f ≡ just x) → is-just ((r x) cs') → Y)
   → ----------------------
  is-just (((lift-read (get-bch B k ?>= d)) >>= r) cs) → Y
use-get-bch B k d r cs h0 = 
  use-is-just-bind (lift-read (get-bch B k ?>= d)) r cs \ x cs' h1 → 
    exist-elim (from-lift-read-get-bch B _ d x _ _ h1) \ f h2 → 
      h0 f x _ (and-left h2) (and-right h2) 

correct-core : ∀ P B N cs → good-bch B → 
  is-just (verify P B N cs) → unsat P B
correct-core P B (suc k) (c ∷ cs) hg = 
  correct-aux P B c 'A' cs
    ( use-is-just-bind read-nat _ cs \ m cs0 h0 → 
        use-is-just-bind read-bool _ cs0 \ b cs1 h1 → 
          use-is-just-bind (lift-read (get-bch B m ?>= break-a b)) (\ f → verify P (f ∷ B) k) cs1 \ f cs2 h2 h3 → 
              exist-elim (from-lift-read-get-bch B m (break-a b) f _ _ h2) 
               \ g h5 → prsv-a P B b _ _ (and-left h5) (and-right h5) 
                 ( correct-core P (f ∷ B) k _ 
                   (good-bch-a B b _ _ (and-left h5) (and-right h5) hg) h3 ) )   
    ( correct-aux P B c 'B' cs 
      ( use-is-just-bind read-nat _ cs \ m cs0 h0 → 
        use-get-bch B m break-b _ cs0 \ f (g , h) cs1 h1 h2 h3 → 
          use-is-just-seq (verify P (g ∷ B) k) _ cs1 
            ( \ _ cs2 hgB hhB → prsv-b P B f g h h1 h2 
              ( correct-core P _ k _ 
                (and-left (good-bch-b B f g h h1 h2 hg)) 
                (eq-just-to-is-just _ _ hgB) ) 
              ( correct-core P _ k _ ((and-right (good-bch-b B f g h h1 h2 hg))) hhB ) ) 
            h3 )
      ( correct-aux P B c 'C' cs 
        ( use-is-just-bind read-nat _ cs \ m cs0 h0 → 
          use-is-just-bind (read-term k) _ cs0 \ t cs1 h1 → 
            use-is-just-pass-if-seq (check-gnd-term 0 t) _ cs1 \ h2 → 
              use-is-just-pass-if-seq (check-nf-term (length B + 1) t) _ cs1 \ h3 → 
                use-get-bch B m (break-c t) _ cs1 \ f g cs2 h4 h5 h6 → {!   !}
            )
        {!   !} ) )

correct : ∀ P N cs → is-just (verify P [] N cs) → unsat-prob P
correct P N cs h0 R F V h1 = 
  exist-elim (correct-core P [] N cs pall-nil h0 R F V h1) 
    \ f → \ h2 → (f , or-elim (and-left h2) (\ h3 → (h3 , and-right h2)) ⊥-elim)  
    
  
