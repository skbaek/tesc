module correct (D : Set) (wit : D) where

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
  renaming (_>>=_ to _o>=_)
  renaming (is-just to is-just-bool)
open import Data.Product
open import Data.Char
  renaming (_==_ to _=c_)
  renaming (_<_ to _<c_)
  -- renaming (show to show-char)
open import Relation.Nullary.Decidable using (toWitness)
open import basic 
open import verify 
open import definitions D

postulate LEM : (A : Set) → Dec A
postulate FX : ∀ {A B : Set} (f g : A → B) (h : ∀ a → f a ≡ f a) → f ≡ g

and-symm : ∀ {A B : Set} → (A ∧ B) → (B ∧ A)
and-symm h = and-rgt h , and-lft h

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

not-elim : ∀ {A B : Set} → A → (¬ A) → B
not-elim h0 h1 = ⊥-elim (h1 h0)

pall-nil : {A : Set} {p : A → Set} → pall p []
pall-nil {A} {p} x = ⊥-elim

fs : Bool → Set
fs true  = ⊥
fs false = ⊤

-- ite-false-eq : ∀ {A : Set} {x y : A} {b : Bool} → 
--   fs b → (if b then x else y) ≡ y
-- ite-false-eq refl = refl

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
      (\ h1 → or-rgt (or-lft _)) 
      \ h1 → or-rgt (or-rgt (suc< _ _ h1))

<-to-<n : ∀ k m → k < m → tr (k <n m) 
<-to-<n 0 (suc m) (0< m) = tt
<-to-<n (suc k) (suc m) (suc< k m h) = <-to-<n k m h

<n-to-< : ∀ k m → tr (k <n m) → k < m
<n-to-< _ 0  ()
<n-to-< 0 (suc m) _ = 0< m 
<n-to-< (suc k) (suc m) h = suc< k m (<n-to-< k m h)

≡-to-=n : ∀ k m → k ≡ m → tr (k =n m) 
≡-to-=n 0 0 refl = tt
≡-to-=n (suc k) (suc m) h = ≡-to-=n k m _ --(suc-inj h) 

=n-to-≡ : ∀ {k m} → tr (k =n m) → k ≡ m
=n-to-≡ {0} {0} _ = refl
=n-to-≡ {0} {suc m} ()
=n-to-≡ {suc k} {0} ()
=n-to-≡ {suc k} {suc m} h = cong suc (=n-to-≡ h)
  
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

tri-eq-lt : ∀ {A : Set} {a b c : A} (k m : Nat) → (k < m) → (tri k a b c m) ≡ a 
tri-eq-lt {A} {a} {b} {c} k m h0 = 
  intro-ite-lem (k <n m) (λ x → x ≡ a) 
    (\ _ → refl) 
    (\ h1 → elim-bool-absurd (<-to-<n k m h0) h1)

tri-eq-eq : ∀ {A : Set} {a b c : A} (k m : Nat) → (k ≡ m) → (tri k a b c m) ≡ b 
tri-eq-eq {A} {a} {b} {c} k m h0 = 
  intro-ite-lem (k <n m) (λ x → x ≡ b) 
    (λ h1 → ⊥-elim (not-<-self m (<n-to-< m m (eq-elim (λ x → tr (x <n m)) h0 h1)))) 
    \ h1 → intro-ite-lem (k =n m) (\ x → x ≡ b) (\ _ → refl) \ h2 → elim-bool-absurd (≡-to-=n k m h0) h2

tri-eq-gt : ∀ {A : Set} {a b c : A} (k m : Nat) → (k > m) → (tri k a b c m) ≡ c 
tri-eq-gt {A} {a} {b} {c} k m h0 = 
  intro-ite-lem (k <n m) (λ x → x ≡ c) 
    (\ h1 → ⊥-elim (<-to-not-> _ _ h0 (<n-to-< _ _ h1))) 
    \ h1 → intro-ite-lem (k =n m) (λ x → x ≡ c) 
      (\ h2 → ⊥-elim (lt-to-not-eq _ _ h0 ( eq-symm (=n-to-≡ h2)))) 
      \ h2 → refl 

tri-elim : ∀ {A : Set} {a b c : A} (k m : Nat) → (P : A → Set) →
  (k < m → P a) → (k ≡ m → P b) → (k > m → P c) → P (tri k a b c m)
tri-elim k m P hl he hg = 
  intro-ite-lem (k <n m) P 
    (\ h0 → hl  (<n-to-< _ _ h0)) 
    \ h0 → intro-ite-lem (k =n m) P 
      (\ h1 → he (=n-to-≡ h1)) 
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
  (f o>= g) ≡ just b → ∃ (\ a → (f ≡ just a) ∧ (g a ≡ just b))

of-bind-eq-just nothing g b = maybe-absurd
of-bind-eq-just (just a) g b = \ h → (a , (refl , h))

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

implies-b : ∀ f g h → break-b f ≡ just (g , h) → f => (bct or g h)
implies-b (bct or f0 f1) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (bct or f0 f1 => bct or x y)) 
    (prod-inj-lft h1) (prod-inj-rgt h1) \ _ _ _ → id
implies-b (bct imp f0 f1) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (bct imp f0 f1 => bct or x y)) 
    (prod-inj-lft h1) (prod-inj-rgt h1) \ R F V → imp-to-not-or
implies-b (not (bct and f0 f1)) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (not (bct and f0 f1) => bct or x y)) 
    (prod-inj-lft h1) (prod-inj-rgt h1) \ R F V → not-and-to-not-or-not
implies-b (not (bct iff f0 f1)) g h h0 = 
  let h1 = just-inj h0 
  in eq-elim-2 (\ x y → (not (bct iff f0 f1) => bct or x y)) 
    (prod-inj-lft h1) (prod-inj-rgt h1) \ R F V → not-and-to-not-or-not

implies-a : ∀ b f g → break-a b f ≡ just g → f => g
implies-a true  (bct and f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-lft h1) 
implies-a false (bct and f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-rgt h1) 
implies-a true  (bct iff f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-lft h1) 
implies-a false (bct iff f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (and-rgt h1) 
implies-a true  (not (bct or f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-or-lft h1) 
implies-a false (not (bct or f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-or-rgt h1) 
implies-a true  (not (bct imp f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-imp-lft h1) 
implies-a false (not (bct imp f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊢ x) (just-inj h0) (not-imp-rgt h1) 

iff-to-not-iff-not : ∀ {A B} → (A ↔ B) → ((¬ A) ↔ (¬ B))
iff-to-not-iff-not h0 = 
  ( (\ ha hb → ⊥-elim (ha (and-rgt h0 hb))) , 
    (\ hb ha → ⊥-elim (hb (and-lft h0 ha))) ) 

or-iff-or : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∨ B0) ↔ (A1 ∨ B1))
or-iff-or ha hb = 
  (\ h0 → or-elim h0 
    (\ h1 → (or-lft (and-lft ha h1))) 
    (\ h1 → (or-rgt (and-lft hb h1)))) , 
  (\ h0 → or-elim h0 
    (\ h1 → (or-lft (and-rgt ha h1))) 
    (\ h1 → (or-rgt (and-rgt hb h1)))) 

iff-symm : ∀ {A B} → (A ↔ B) → (B ↔ A) 
iff-symm h0 = (λ h1 → and-rgt h0 h1) , (λ h1 → and-lft h0 h1)

iff-trans : ∀ {A B C} → (A ↔ B) → (B ↔ C) → (A ↔ C)
iff-trans h0 h1 = 
  (λ h2 → and-lft h1 (and-lft h0 h2)) , 
  (λ h2 → and-rgt h0 (and-rgt h1 h2))

and-iff-and : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∧ B0) ↔ (A1 ∧ B1))
and-iff-and ha hb = 
  (\ h0 → (and-lft ha (and-lft h0) , and-lft hb (and-rgt h0))) , 
  (\ h0 → (and-rgt ha (and-lft h0) , and-rgt hb (and-rgt h0)))

imp-iff-imp : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 → B0) ↔ (A1 → B1))
imp-iff-imp ha hb = 
  (\ h0 h1 → and-lft hb (h0 (and-rgt ha h1))) , 
  (\ h0 h1 → and-rgt hb (h0 (and-lft ha h1)))

iff-iff-iff : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ↔ B0) ↔ (A1 ↔ B1))
iff-iff-iff ha hb =  
  (λ h0 → iff-trans (iff-symm ha) (iff-trans h0 hb)) ,
  (λ h0 → iff-trans ha (iff-trans h0 (iff-symm hb)))

fa-iff-fa : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∀ a → P a) ↔ (∀ a → Q a))
fa-iff-fa h0 = ((\ h1 a → and-lft (h0 a) (h1 a)) , (\h1 a → and-rgt (h0 a) (h1 a)))

ex-iff-ex : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∃ P) ↔ (∃ Q))
ex-iff-ex h0 = 
  (\ h1 → ex-elim h1 (\ a h2 → a , and-lft (h0 a) h2)) , 
  (\ h2 → ex-elim h2 (\ a h2 → a , and-rgt (h0 a) h2))

termoid-val-incr : ∀ b F V d (t : Termoid b) → termoid-val F (V / 0 ↦ d) (incr-var t) ≡ termoid-val F V t 
termoid-val-incr false F V d (var k) = refl
termoid-val-incr false F V d (fun f ts) = 
  cong (F f) (termoid-val-incr true F V d ts)
termoid-val-incr true  F V d nil = refl
termoid-val-incr true  F V d (cons t ts) = 
  cong2 _∷_ 
    (termoid-val-incr false F V d t) 
    (termoid-val-incr true F V d ts)

term-val-incr : ∀ F V d t → term-val F (V / 0 ↦ d) (incr-var t) ≡ term-val F V t 
term-val-incr = termoid-val-incr false

update-update : ∀ V k d e → ((V / 0 ↦ e ) / (suc k) ↦ d) ≡ ((V / k ↦ d) / 0 ↦ e) 
update-update V k d e = FX _ _ \ { 0 → refl ; (suc m) → refl }

dni : ∀ {A} → A → (¬ (¬ A))
dni h0 h1 = h1 h0

dne : ∀ {A} → (¬ ¬ A) → A 
dne {A} h0 = use-lem A id λ h1 → ⊥-elim (h0 h1)

iff-refl : ∀ {A} → (A ↔ A)
iff-refl = (id , id)

not-iff-not-to-iff : ∀ {A B} → ((¬ A) ↔ (¬ B)) → (A ↔ B)
not-iff-not-to-iff h0 = 
  (λ h1 → dne (λ h2 → and-rgt h0 h2 h1)) ,
  (λ h1 → dne (λ h2 → and-lft h0 h2 h1)) 

eq-to-iff : ∀ {A : Set} (P : A → Set) (x y : A) → x ≡ y → ((P x) ↔ (P y))
eq-to-iff P x y refl = iff-refl  

termoid-val-subst : ∀ (F : FA) (V : VA) (k : Nat) (b : Bool) (s : Term) (t : Termoid b) → 
  (termoid-val F (V / k ↦ term-val F V s) t) ≡ (termoid-val F V (subst-termoid k s t))
termoid-val-subst F V k true s nil = refl
termoid-val-subst F V k true s (cons t ts) = 
  cong2 _∷_ (termoid-val-subst F V k false s t) 
    (termoid-val-subst F V k true s ts)
termoid-val-subst F V k false s (var m) = 
  tri-elim k m 
    (λ x → (V / k ↦ term-val F V s) m ≡ termoid-val F V x)
     (\ h0 → eq-trans _ (tri-eq-lt k m h0) refl) 
    (\ h0 → eq-trans _ (tri-eq-eq k m h0) refl) 
    (\ h0 → eq-trans _ (tri-eq-gt k m h0) refl)
termoid-val-subst F V k false s (fun f ts) = 
  cong (F f) (termoid-val-subst F V k true _ ts)

qtf-iff-qtf : ∀ b {R0 R1 F0 F1 V0 V1 f0 f1} → 
  (∀ d → (R0 , F0 , (V0 / 0 ↦ d) ⊢ f0) ↔ (R1 , F1 , (V1 / 0 ↦ d) ⊢ f1)) →  
  ((R0 , F0 , V0 ⊢ qtf b f0) ↔ (R1 , F1 , V1 ⊢ qtf b f1))   
qtf-iff-qtf true h0 = ex-iff-ex h0
qtf-iff-qtf false h0 = fa-iff-fa h0

bct-iff-bct : ∀ b {R0 R1 F0 F1 V0 V1 f0 f1 g0 g1} → 
  ((R0 , F0 , V0 ⊢ f0) ↔ (R1 , F1 , V1 ⊢ f1)) →  
  ((R0 , F0 , V0 ⊢ g0) ↔ (R1 , F1 , V1 ⊢ g1)) →  
  ((R0 , F0 , V0 ⊢ bct b f0 g0) ↔ (R1 , F1 , V1 ⊢ bct b f1 g1)) 
bct-iff-bct or h0 h1 = or-iff-or h0 h1
bct-iff-bct and h0 h1 = and-iff-and h0 h1
bct-iff-bct imp h0 h1 = imp-iff-imp h0 h1
bct-iff-bct iff h0 h1 = iff-iff-iff h0 h1

holds-subst : ∀ R F V k t f → 
  ((R , F , (V / k ↦ (term-val F V t)) ⊢ f) ↔ (R , F , V ⊢ subst-form k t f))
holds-subst R F V k t (rel r ts) = 
  eq-to-iff (\ x → tr (R r x)) _ _ (termoid-val-subst F V k true _ ts)
holds-subst R F V k t (cst b) = ( id , id )
holds-subst R F V k t (not f) = iff-to-not-iff-not (holds-subst _ _ _ k t f)
holds-subst R F V k t (bct b f g) = 
  bct-iff-bct b (holds-subst _ _ _ k t f) (holds-subst _ _ _ k t g) 
holds-subst R F V k t (qtf b f) = 
  qtf-iff-qtf b 
    λ d →  
      eq-elim 
        (\ x → ((R , F , x ⊢ f) ↔ (R , F , V / 0 ↦ d ⊢ subst-form (suc k) (incr-var t) f))) 
        (update-update V k (term-val F V t) d) 
        ( eq-elim 
            ( λ x → 
                (R , F , (V / 0 ↦ d) / suc k ↦ x ⊢ f) ↔ 
                  (R , F , V / 0 ↦ d ⊢ subst-form (suc k) (incr-var t) f) ) 
            (term-val-incr F V d t) 
            (holds-subst R F _ (suc k) (incr-var t) f) )

implies-c : ∀ t f g → break-c t f ≡ just g → f => g
implies-c t (qtf false f) g h0 R F V h1 = 
  let h2 = just-inj h0 in 
  let h3 = h1 (term-val F V t) in
  eq-elim (λ x → R , F , V ⊢ x) h2 (and-lft (holds-subst R F V 0 t f) h3)
implies-c t (not (qtf true f)) g h0 R F V h1 = 
  let h2 = just-inj h0 in 
  eq-elim (λ x → R , F , V ⊢ x) h2 
    λ h3 → h1 (term-val F V t , and-rgt (holds-subst R F V 0 t f) h3)

from-tr-band-lft : ∀ a b → tr (a && b) → tr a 
from-tr-band-lft true _ _ = tt

from-tr-band-rgt : ∀ a b → tr (a && b) → tr b 
from-tr-band-rgt _ true _ = tt
from-tr-band-rgt true false ()

from-checks-good-ftr : ∀ k f → tr (chk-good-ftr k f) → good-ftr k f
from-checks-good-ftr k (nf m) h = <n-to-< _ _ h
from-checks-good-ftr _ (sf _) _ = tt

checks-good : ∀ {b} k (t : Termoid b) → tr (chk-good-termoid k t) → good-termoid k t 
checks-good {true} _ nil _ = tt
checks-good {true} k (cons t ts) h0 = 
  checks-good _ _ (from-tr-band-lft _ _ h0) , checks-good _ _ (from-tr-band-rgt _ _ h0)
checks-good {false} k (var m) h0 = tt
checks-good {false} k (fun f ts) h0 =
  from-checks-good-ftr _ _ (from-tr-band-lft _ _ h0) , 
  checks-good _ _ (from-tr-band-rgt _ _ h0)

checks-good-form : ∀ k f → tr (chk-good-form k f) → good-form k f  
checks-good-form _ (cst _) _ = tt
checks-good-form k (bct _ f g) h0 =  
  (checks-good-form k f (from-tr-band-lft _ _ h0)) , 
  (checks-good-form k g (from-tr-band-rgt _ _ h0))
checks-good-form k (not f) h0 = checks-good-form k f h0
checks-good-form k (qtf _ f) h0 = checks-good-form k f h0
checks-good-form k (rel r ts) h0 = 
  from-checks-good-ftr _ r (from-tr-band-lft _ _ h0) , 
  checks-good k ts (from-tr-band-rgt _ _ h0) 

good-ftr-suc : ∀ k f → good-ftr k f → good-ftr (suc k) f
good-ftr-suc k (nf m) h = <-to-<-suc m k h
good-ftr-suc _ (sf _) _ = tt

good-termoid-suc : ∀ {b} k (f : Termoid b) → good-termoid k f → good-termoid (suc k) f
good-termoid-suc {false} _ (var _) _ = tt 
good-termoid-suc {false} k (fun f ts) h0 = 
  good-ftr-suc k f (and-lft h0) , good-termoid-suc k ts (and-rgt h0) 
good-termoid-suc {true} _ nil _ = tt
good-termoid-suc {true} k (cons t ts) h0 = 
  good-termoid-suc _ t (and-lft h0) , good-termoid-suc k ts (and-rgt h0)

good-form-suc : ∀ k f → good-form k f → good-form (suc k) f
good-form-suc k (cst _) h0 = tt 
good-form-suc k (rel r ts) h0 = 
   ( good-ftr-suc _ _ (and-lft h0) , 
     good-termoid-suc _ _ (and-rgt h0) ) 
good-form-suc k (not f) h0 = good-form-suc k f h0
good-form-suc k (bct _ f g) h0 =
  (good-form-suc k f (and-lft h0)) , 
  (good-form-suc k g (and-rgt h0))
good-form-suc k (qtf _ f) h0 = good-form-suc k f h0

good-bch-cons : ∀ f B → good-form (suc (length B)) f → good-bch B → good-bch (f ∷ B)
good-bch-cons f B h0 h1 g = 
  or-elim' (\ h2 → eq-elim _ (eq-symm h2) h0) (\ h2 → good-form-suc _ g (h1 _ h2)) 

prsv-implies : ∀ P B f g → f ∈ B → f => g → unsat P (g ∷ B) → unsat P B 
prsv-implies P B f g h0 h1 h2 R F V h3 = 
  ex-elim (h2 R F V h3) ( \ h h4 → let h5 = and-rgt h4 
    in or-elim (and-lft h4) 
      (\ h6 → (h , (or-lft h6 , h5))) 
      \ h6 → or-elim h6 
        (\ h7 → (f , (or-rgt h0 , modus-tollens 
           (\ h8 → eq-elim (\ x → R , F , V ⊢ x) (eq-symm h7) 
             (h1 R F V h8))
          h5) ) ) 
        \ h7 → (h , (or-rgt h7 , h5)) )

prsv-a : ∀ P B b f g → f ∈ B → (break-a b f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-a P B b f g h0 h1 = prsv-implies P B f g h0 (implies-a _ _ _ h1) 

unsat-or-cons : ∀ P B f g → unsat P (f ∷ B) → unsat P (g ∷ B) → unsat P (bct or f g ∷ B)
unsat-or-cons P B f g hf hg R F V hs = ex-elim (hf R F V hs) \ f' h0 → 
  or-elim (and-lft h0) 
    (\ h1 → (f' , (or-lft h1 , and-rgt h0))) 
    ( or-elim' 
      ( \ h2 → ex-elim (hg R F V hs) \ g' h3 → 
        or-elim (and-lft h3) 
          (\ h4 → (g' , (or-lft h4 , and-rgt h3))) 
          ( or-elim' 
            ( \ h4 → ( bct or f g , 
              ( or-rgt (or-lft refl), 
                or-elim' 
                  (eq-elim (λ x → ¬ (R , F , V ⊢ x)) h2 (and-rgt h0)) 
                  (eq-elim (λ x → ¬ (R , F , V ⊢ x)) h4 (and-rgt h3)) ) ) ) 
            (\ h4 → (g' , (or-rgt (or-rgt h4) , and-rgt h3))) )
      ) 
      (\ h1 → (f' , (or-rgt (or-rgt h1) , and-rgt h0))) )

prsv-b : ∀ P B f g h → f ∈ B → (break-b f ≡ just (g , h)) → 
  unsat P (g ∷ B) → unsat P (h ∷ B) → unsat P B 
prsv-b P B f g h h0 h1 h2 h3 = prsv-implies P B f (bct or g h) 
  h0 (implies-b _ _ _ h1) (unsat-or-cons _ _ _ _ h2 h3)

prsv-c : ∀ P B t f g → f ∈ B → (break-c t f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-c P B t f g h1 h2 h3 = prsv-implies P B f g h1 (implies-c t f g h2) h3

not-ex-to-fa-not : ∀ {A} (P : A → Set) → (¬ ∃ P) → (∀ x → ¬ P x)
not-ex-to-fa-not P h0 a h1 = h0 (a , h1)

not-fa-to-ex-not : ∀ {A} (P : A → Set) → ¬ (∀ x → P x) → ∃ λ x → ¬ P x
not-fa-to-ex-not P h0 = dne (λ h1 → h0 (λ a → dne (λ h2 → h1 (a , h2))))

not-and-lft : ∀ {A} {B} → ¬ (A ∧ B) → A → ¬ B  
not-and-lft h0 h1 h2 = h0 (h1 , h2)

sat-or-unsat : ∀ P B → (sat P B ∨ unsat P B)
sat-or-unsat P B = use-lem (unsat P B) or-rgt λ h0 →  
  ex-elim (not-fa-to-ex-not _ h0) λ R h1 → 
    ex-elim (not-fa-to-ex-not _ h1) λ F h2 → 
      ex-elim (not-fa-to-ex-not _ h2) λ V h3 → 
        ex-elim (not-fa-to-ex-not _ h3) λ h4 h5 → 
          or-lft ( R , F , V , h4 , 
            (λ f h6 → dne (λ h7 → ⊥-elim (h5 (f , h6 , h7)))) )

unsat-to-not-sat : ∀ P B → unsat P B → ¬ sat P B 
unsat-to-not-sat P B h0 h1 =
  ex-elim-3 h1 
    λ R F V (hR , h2) → 
      ex-elim (h0 R F V hR) 
        λ f (h3 , h4) → h4 (h2 f h3)

tr-to-ite-eq : ∀ {A : Set} {b} {a0 a1 : A} → tr b → (if b then a0 else a1) ≡ a0
tr-to-ite-eq {_} {true} _ = refl  

cons-eq : ∀ {A : Set} (a0 a1 : A) (as0 as1 : List A) →
  a0 ≡ a1 → as0 ≡ as1 → (a0 ∷ as0) ≡ (a1 ∷ as1) 
cons-eq a0 a1 as0 as1 refl refl = refl

term-val-update-par : ∀ F k d V → 
  term-val (F / nf k ↦f const-fn d) V (par k) ≡ d
term-val-update-par F k d V = 
  let h0 = tr-to-ite-eq {List D → D} {k =n k} {λ _ → d} {F (nf k)} (≡-to-=n k k refl) in 
  eq-elim (λ x → x [] ≡ d) (eq-symm h0) refl 

from-break-n-eq-just : ∀ f g → break-n f ≡ just g → f ≡ (not (not g)) 
from-break-n-eq-just (not (not f)) g h0 = cong not (cong not (just-inj h0))

char-eq-to-eq : ∀ c0 c1 → tr (c0 =c c1) → c0 ≡ c1 
char-eq-to-eq c0 c1 = toWitness

chars-eq-to-eq : ∀ cs0 cs1 → tr (cs0 =cs cs1) → cs0 ≡ cs1 
chars-eq-to-eq [] [] _ = refl
chars-eq-to-eq (c0 ∷ cs0) (c1 ∷ cs1) h0 = 
  cong2 _∷_ 
    (toWitness (from-tr-band-lft (c0 =c c1) _ h0)) 
    (chars-eq-to-eq cs0 cs1 (from-tr-band-rgt _ _ h0))

ftr-eq-to-eq : ∀ f g → tr (f =ft g) → f ≡ g
ftr-eq-to-eq (nf k) (nf m) h0 = cong nf (=n-to-≡ h0)
ftr-eq-to-eq (sf s) (sf t) h0 = cong sf (chars-eq-to-eq  _ _ h0)

elim-ite-lem : ∀ {A B : Set} (P : A → Set) (b : Bool) (a0 a1 : A) → 
  (tr b → P a0 → B) → (fs b → P a1 → B) → P (if b then a0 else a1) → B
elim-ite-lem _ true _ _ h0 _ h1 = h0 tt h1
elim-ite-lem _ false _ _ _ h0 h1 = h0 tt h1 -- h0 refl h1

_≠_ : {A : Set} → A → A → Set 
x ≠ y = ¬ (x ≡ y)

nf-inj : ∀ {k m} → nf k ≡ nf m → k ≡ m 
nf-inj refl = refl

ex-falso : ∀ {A B : Set} → A → ¬ A → B
ex-falso h0 h1 = ⊥-elim (h1 h0)

good-to-ftr-neq : ∀ k f → (good-ftr k f) → f ≠ nf k
good-to-ftr-neq k (nf m) h0 h1 = 
  ex-falso h0 (eq-elim (λ x → ¬ (m < x)) (nf-inj h1) (not-<-self m))
good-to-ftr-neq k (sf m) _ ()

good-to-termoid-val-eq : ∀ {b} F V k fn (t : Termoid b) → (good-termoid k t) → 
  (termoid-val (F / nf k ↦f fn) V t) ≡ (termoid-val F V t) 
good-to-termoid-val-eq {true} F V k fn nil h0 = refl
good-to-termoid-val-eq {true} F V k fn (cons t ts) h0 = 
  cons-eq  _ _ _ _
    (good-to-termoid-val-eq F V k fn t (and-lft h0))  
    (good-to-termoid-val-eq F V k fn ts (and-rgt h0))
good-to-termoid-val-eq F V k fn (var m) h0 = refl
good-to-termoid-val-eq F V k fn (fun f ts) h0 = 
  cong2 {Fn} {List D} {D} (λ x y → x y) {(F / nf k ↦f fn) f} {F f} 
    ( intro-ite-lem {Fn} (nf k =ft f) (λ x → x ≡ F f) 
        ( λ h1 → 
            let h2 = eq-symm (ftr-eq-to-eq _ _ h1) in 
            let h3 : k < k  
                h3 = (and-lft (eq-elim {_} {f} {nf k} (λ x → good-termoid k (fun x ts)) h2 h0)) in
            ⊥-elim (not-<-self k h3) ) 
        λ _ → refl )
    (good-to-termoid-val-eq F V k fn ts (and-rgt h0))

good-to-holds-update-iff : ∀ R F V k fn f → good-form k f → 
  (R , (F / nf k ↦f fn), V ⊢ f) ↔ (R , F , V ⊢ f)
good-to-holds-update-iff R F V k fn (cst b) _ = iff-refl
good-to-holds-update-iff R F V k fn (not f) h0 = 
  iff-to-not-iff-not (good-to-holds-update-iff R F V k fn f h0)
good-to-holds-update-iff R F V k fn (bct b f g) h0 = 
  bct-iff-bct b 
    (good-to-holds-update-iff R F V k fn f (and-lft h0)) 
    (good-to-holds-update-iff R F V k fn g (and-rgt h0)) 
good-to-holds-update-iff R F V k fn (qtf b f) h0 = 
  qtf-iff-qtf b 
    λ d → good-to-holds-update-iff R F _ k fn f h0
good-to-holds-update-iff R F V k fn (rel r ts) h0 = 
  eq-to-iff (λ x → tr (R r x)) _ _ (good-to-termoid-val-eq F V k fn ts (and-rgt h0)) 
  
extend : List D → VA 
extend [] _ = wit
extend (d ∷ _) 0 = d
extend (_ ∷ ds) (suc k) = extend ds k

skolem-fn-asc : RA → FA → Form → Fn
skolem-fn-asc R F f ds = 
  use-lem (R , F , extend ds ⊢ ∃* f) 
    (ex-elim' (λ d _ → d)) 
    (λ _ → wit)

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

skolem-fn-desc : RA → FA → Form → Fn
skolem-fn-desc R F f ds = skolem-fn-asc R F f (reverse ds) 

trunc : Nat → VA → List D
trunc 0 _ = []
trunc (suc k) V = V 0 ∷ trunc k (↓ V)

intro-use-lem : ∀ {A B : Set} (C : B → Set) {f : A → B} {g : (¬ A) → B} → 
  (∀ (x : A) → C (f x)) → (∀ (x : ¬ A) → C (g x)) → C (use-lem A f g) 
intro-use-lem {A} {B} C {f} {g} hf hg with LEM A  
... | (yes h0) = hf h0 
... | (no h0) = hg h0 

intro-use-lem-yes : ∀ {A B : Set} (C : B → Set) {f : A → B} {g : (¬ A) → B} → 
  (∀ (x : A) → C (f x)) → A → C (use-lem A f g) 
intro-use-lem-yes {A} {B} C {f} {g} hf hA = intro-use-lem C hf λ h0 → ⊥-elim (h0 hA)

foo' : ∀ R F f ds → (R , F , extend ds ⊢ ∃* f) → 
  R , F , (extend ds) / 0 ↦ (skolem-fn-asc R F f ds) ⊢ f  
foo' R F f ds h0 = 
  intro-use-lem-yes (λ x → R , F , extend ds / 0 ↦ x ⊢ f) 
    (λ (d , h1) → h1) 
    h0 

foo : ∀ R F f ds → (R , F , extend ds ⊢ ∃* f) → 
  R , F , (extend ds) / 0 ↦ (skolem-fn-desc R F f (reverse ds)) ⊢ f  
foo R F f ds h0 = 
  let h1 = foo' R F f ds h0 in 
  eq-elim' (λ x → R , F , extend ds / 0 ↦ skolem-fn-asc R F f x ⊢ f) (reverse-reverse ds) h1 

eq-va-lt : Nat → VA → VA → Set
eq-va-lt k V0 V1 = ∀ m → m < k → V0 m ≡ V1 m

eq-va-lt-suc : ∀ k V0 V1 d0 d1 → eq-va-lt k V0 V1 → d0 ≡ d1 → 
  eq-va-lt (suc k) (V0 / 0 ↦ d0) (V1 / 0 ↦ d1)
eq-va-lt-suc k V0 V1 d0 d1 h0 h1 0 h2 = h1
eq-va-lt-suc k V0 V1 d0 d1 h0 h1 (suc m) (suc< _ _ h2) = h0 m h2

bart : ∀ {b} F V0 V1 k (t : Termoid b) → eq-va-lt k V0 V1 → vars-lt-termoid k t → 
  (termoid-val F V0 t) ≡ (termoid-val F V1 t) 
bart {true} F V0 V1 k nil _ _ = refl
bart {true} F V0 V1 k (cons t ts) h0 h1 = 
  cong2 _∷_ (bart F V0 V1 k t h0 (fst h1)) (bart F V0 V1 k ts h0 (snd h1))
bart {false} F V0 V1 k (var m) h0 h1 = h0 m h1
bart {false} F V0 V1 k (fun f ts) h0 h1 = cong (F f) (bart F V0 V1 k ts h0 h1)

bar : ∀ R F V0 V1 k f → eq-va-lt k V0 V1 → vars-lt-form k f → 
  (R , F , V0 ⊢ f) ↔ (R , F , V1 ⊢ f) 
bar R F V0 V1 k (cst b) _ _ = iff-refl
bar R F V0 V1 k (not f) h0 h1 = iff-to-not-iff-not (bar R F V0 V1 k f h0 h1)
bar R F V0 V1 k (bct b f g) h0 h1 = 
  bct-iff-bct b (bar R F V0 V1 k f h0 (fst h1)) (bar R F V0 V1 k g h0 (snd h1))
bar R F V0 V1 k (qtf b f) h0 h1 = 
  qtf-iff-qtf b λ d → bar R F _ _ (suc k) f (eq-va-lt-suc k V0 V1 d d h0 refl) h1
bar R F V0 V1 k (rel r ts) h0 h1 = 
  eq-to-iff (λ x → tr (R r x)) (terms-val F V0 ts) _ (bart F V0 V1 k ts h0 h1)

eq-va-lt-extend-trunc : ∀ V k → eq-va-lt k (extend (trunc k V)) V
eq-va-lt-extend-trunc V 0 m ()
eq-va-lt-extend-trunc V (suc k ) 0 (0< _) = refl
eq-va-lt-extend-trunc V (suc k ) (suc m) (suc< _ _ h0) = eq-va-lt-extend-trunc (↓ V) k m h0

fa-update-eq : ∀ F k fn → fn ≡ (F / nf k ↦f fn) (nf k) 
fa-update-eq F k fn = eq-symm (tr-to-ite-eq {_} {nf k =ft nf k} (≡-to-=n k k refl)) --(tr-to-ite-eq {!  refl !})
 
qux-core : ∀ F V m → 
  termoid-val F (↓ V) (vars-desc m) ∷ʳ V 0 ≡ termoid-val F V (cons (var m) (vars-desc m))
qux-core F V 0 = refl 
qux-core F V (suc m) = cong2 _∷_ refl (qux-core F _ m) 

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
  cong2 _∷_ h1 h3 , h4

reverse-inj : ∀ {A : Set} (as0 as1 : List A) → reverse as0 ≡ reverse as1 → as0 ≡ as1  
reverse-inj [] [] refl = refl
reverse-inj (a0 ∷ as0) [] h0 = ⊥-elim (not-app-eq-nil _ _ _ (eq-trans _ (eq-symm (reverse-cons a0 as0)) h0))
reverse-inj [] (a1 ∷ as1) h0 = ⊥-elim (not-app-eq-nil _ _ _ (eq-symm (eq-trans _ h0 ( (reverse-cons a1 as1))))) 
reverse-inj (a0 ∷ as0) (a1 ∷ as1) h0 = 
  let h3 = eq-symm (reverse-cons a0 as0) in
  let h4 = reverse-cons a1 as1 in
  let (h1 , h2) = snoc-inj a0 a1 (reverse as0) (reverse as1) (eq-trans _ h3 (eq-trans _ h0 h4)) in 
  cong2 _∷_ h2 (reverse-inj _ _ h1)

termoid-val-rev-terms : ∀ F V ts0 ts1 → 
  termoid-val F V (rev-terms ts0 ts1) ≡  reverseAcc (termoid-val F V ts1) (termoid-val F V ts0) 
termoid-val-rev-terms F V nil ts1 = refl 
termoid-val-rev-terms F V (cons t ts0) ts1 = termoid-val-rev-terms F V ts0 (cons t ts1) 

-- qux'-core : ∀ F V m → 
--   V 0 ∷ termoid-val F (↓ V) (vars-asc m) ≡ termoid-val F V (vars-asc (suc m))
-- qux'-core F V 0 = refl 
-- qux'-core F V (suc m) = {!   !} 


qux : ∀ F V m → reverse (trunc m V) ≡ termoid-val F V (vars-desc m)
qux F V 0 = refl
qux F V (suc m) = eq-trans _ (reverse-cons (V 0) (trunc m (↓ V))) 
  (eq-trans ((termoid-val F (↓ V) (vars-desc m)) ∷ʳ V 0) 
  (cong (λ x → x ∷ʳ V 0) (qux F (↓ V) m)) (qux-core F _ m))

qux' : ∀ F V m → (trunc m V) ≡ termoid-val F V (vars-asc m)
qux' F V m = 
  reverse-inj _ _ 
    ( eq-trans _ (qux F V m) 
        ( eq-trans _
            (eq-symm (reverse-reverse (termoid-val F V (vars-desc m)))) 
            ( cong reverse {_} {termoid-val F V (vars-asc m)} 
                (eq-symm (termoid-val-rev-terms F V (vars-desc m) nil)) ) ) )

cong-fun-arg : ∀ {A B : Set} {x0 x1 : A → B} {y0 y1 : A} → 
  x0 ≡ x1 → y0 ≡ y1 → (x0 y0 ≡ x1 y1)
cong-fun-arg refl refl = refl

data only-vars : ∀ {b} → Termoid b → Set where 
  only-vars-nil : only-vars nil
  only-vars-var : ∀ k → only-vars (var k)
  only-vars-cons : ∀ t ts → only-vars t → only-vars ts → only-vars (cons t ts)

only-vars-to-eq : ∀ {b} F0 F1 V (t : Termoid b) → only-vars t → termoid-val F0 V t ≡ termoid-val F1 V t
only-vars-to-eq F0 F1 V nil _ = refl
only-vars-to-eq F0 F1 V (var _) _ = refl
only-vars-to-eq F0 F1 V (cons t ts) (only-vars-cons _ _ h0 h1) = 
  cong2 _∷_ (only-vars-to-eq _ _ _ t h0) (only-vars-to-eq _ _ _ ts h1)

only-vars-vars-desc : ∀ k → only-vars (vars-desc k)
only-vars-vars-desc 0 = only-vars-nil
only-vars-vars-desc (suc k) = only-vars-cons _ _ (only-vars-var k) (only-vars-vars-desc k)

only-vars-rev-terms : ∀ ts0 ts1 → only-vars ts0 → only-vars ts1 → only-vars (rev-terms ts0 ts1)
only-vars-rev-terms nil ts1 h0 h1 = h1
only-vars-rev-terms (cons t ts0) ts1 (only-vars-cons _ _ h0 h1) h2 = 
  only-vars-rev-terms ts0 (cons t ts1) h1 (only-vars-cons _ _ h0 h2)

only-vars-vars-asc : ∀ k → only-vars (vars-asc k)
only-vars-vars-asc k = only-vars-rev-terms (vars-desc k) nil (only-vars-vars-desc k) only-vars-nil 

val-vars-asc-eq : ∀ F0 F1 V k → termoid-val F0 V (vars-asc k) ≡ termoid-val F1 V (vars-asc k) 
val-vars-asc-eq F0 F1 V k = only-vars-to-eq _ _ _ _  (only-vars-vars-asc k)

val-vars-desc-eq : ∀ F0 F1 V k → termoid-val F0 V (vars-desc k) ≡ termoid-val F1 V (vars-desc k) 
val-vars-desc-eq F0 F1 V k = only-vars-to-eq _ _ _ _  (only-vars-vars-desc k)

quz' : ∀ R F V f k m →
  skolem-fn-asc R F f (trunc m V) ≡
    term-val (F / nf k ↦f skolem-fn-asc R F f) V (skolem-term-asc k m)
quz' R F V f k m = 
  eq-trans _ 
    (cong (skolem-fn-asc R F f) {trunc m V} (qux' F V m))
    ( cong-fun-arg {_} {_} {skolem-fn-asc R F f} {_} 
        {termoid-val F V (vars-asc m)} {termoid-val _ V (vars-asc m)} 
        (fa-update-eq F k _) 
        (val-vars-asc-eq _ _ V m) )

quz : ∀ R F V f k m →
  skolem-fn-desc R F f (reverse (trunc m V)) ≡
    term-val (F / nf k ↦f skolem-fn-desc R F f) V (skolem-term-desc k m)
quz R F V f k m = 
  eq-trans _ 
    (cong (skolem-fn-desc R F f) {reverse (trunc m V)} (qux F V m))
    ( cong-fun-arg {_} {_} {skolem-fn-desc R F f} {_} 
        {termoid-val F V (vars-desc m)} {termoid-val _ V (vars-desc m)} 
        (fa-update-eq F k _) (val-vars-desc-eq _ _ V m) ) 

eq-va-lt-symm : ∀ k V0 V1 → eq-va-lt k V0 V1 → eq-va-lt k V1 V0 
eq-va-lt-symm k V0 V1 h0 m h1 = eq-symm (h0 m h1)

skolem-fn-asc-aux : ∀ R F V k m f → good-form k f → 
  vars-lt-form (suc m) f → (R , F , V ⊢ ∃* f) → 
  R , (F / (nf k) ↦f skolem-fn-asc R F f) , V ⊢ subst-form 0 (skolem-term-asc k m) f
skolem-fn-asc-aux R F V k m f hf h0 h1 = 
  and-lft (holds-subst R _ V 0 (skolem-term-asc k m) f) 
    (
      let h2 : R , F , extend (trunc m V) ⊢ ∃* f 
          h2 = and-lft (bar  R F _ (extend (trunc m V)) m (∃* f) (eq-va-lt-symm _ _ _ (eq-va-lt-extend-trunc V m)) h0) h1 in
      let h3 = foo' R F f (trunc m V) h2 in 
      and-rgt (good-to-holds-update-iff R F _ k _ f hf) 
       ( and-lft 
            ( bar R F _ _ (suc m) f 
                (eq-va-lt-suc m _ _ _ _ (eq-va-lt-extend-trunc V m)  (quz' R F V f k m))
                h0 ) h3 )
   ) 

skolem-fn-desc-aux : ∀ R F V k m f → good-form k f → 
  vars-lt-form (suc m) f → (R , F , V ⊢ ∃* f) → 
  R , (F / (nf k) ↦f skolem-fn-desc R F f) , V ⊢ subst-form 0 (skolem-term-desc k m) f
skolem-fn-desc-aux R F V k m f hf h0 h1 = 
  and-lft (holds-subst R _ V 0 (skolem-term-desc k m) f) 
    (
      let h2 : R , F , extend (trunc m V) ⊢ ∃* f 
          h2 = and-lft (bar  R F _ (extend (trunc m V)) m (∃* f) (eq-va-lt-symm _ _ _ (eq-va-lt-extend-trunc V m)) h0) h1 in
      let h3 = foo R F f (trunc m V) h2 in 
      and-rgt (good-to-holds-update-iff R F _ k _ f hf) 
        ( and-lft 
            ( bar R F _ _ (suc m) f 
                (eq-va-lt-suc m _ _ _ _ (eq-va-lt-extend-trunc V m)  (quz R F V f k m))
                h0 ) h3 )
    )

prsv-t-pred-def : ∀ R F V k m f → pred-def k m f → ∃ λ rl → (R / (nf k) ↦r rl) , F , V ⊢ f 
prsv-t-pred-def R F V k m _ (pred-def-fa k m f h0) = 
  {! (prsv-t-pred-def R F )  !}

prsv-t-choice : ∀ R F k m f → choice k m f → ∃ λ fn → ∀ V → R , F / (nf k) ↦f fn , V ⊢ f 
prsv-t-choice R F k m _ (choice-fa k m f h0) = 
  ex-elim (prsv-t-choice R F k (suc m) f h0) λ fn h1 → fn , λ V d → h1 (V / 0 ↦ d)
prsv-t-choice R F k m _ (choice-imp-asc k m f h0 h1) = 
  skolem-fn-asc R F f , λ V h2 → 
    let h3 : R , F , V ⊢ ∃* f 
        h3 = and-lft (good-to-holds-update-iff R F V k _ (∃* f) h0) h2 in 
    skolem-fn-asc-aux R _ V k m f h0 h1 h3 
prsv-t-choice R F k m _ (choice-imp-desc k m f h0 h1) = 
  skolem-fn-desc R F f , λ V h2 → 
    let h3 : R , F , V ⊢ ∃* f 
        h3 = and-lft (good-to-holds-update-iff R F V k _ (∃* f) h0) h2 in 
    skolem-fn-desc-aux R _ V k m f h0 h1 h3 

prsv-d-aux : ∀ R F V k f g → good-form k f → break-d k f ≡ just g → 
  R , F , V ⊢ f → ∃ λ d → R , F / (nf k) ↦f (const-fn d) , V ⊢ g 
prsv-d-aux R F V k (qtf true f) g h0 h1 h2 = 
  ex-elim h2 λ d h3 → let F' = (F / (nf k) ↦f (const-fn d)) in 
    d , eq-elim (λ x → R , F' , V ⊢ x) (just-inj h1)
      ( and-lft (holds-subst R F' V 0 (par k) f) 
        ( eq-elim (λ x → R , F' , V / 0 ↦ x ⊢ f) 
          ( eq-symm (term-val-update-par F k d V)) 
            (and-rgt (good-to-holds-update-iff _ _ _ _ _ f h0) h3) ) )
prsv-d-aux R F V k (not (qtf false f)) g h0 h1 h2 = 
  let h2' = not-fa-to-ex-not _ h2 in 
  ex-elim h2' λ d h3 → let F' = (F / (nf k) ↦f (const-fn d)) in 
    d , eq-elim (λ x → R , F' , V ⊢ x) (just-inj h1) λ hc → h3 
     let h4 = and-rgt (holds-subst R F' V 0 (par k) f) hc in 
     let h5 = and-lft (good-to-holds-update-iff R F _ k (const-fn d) f h0) h4 in 
     eq-elim (λ x → R , F , V / 0 ↦ x ⊢ f) (term-val-update-par F k d V) h5

sats-to-sats : ∀ P B R F V fn f → good-prob P → good-bch B → 
  (R , F / (nf (length B)) ↦f fn , V ⊢ f) → sats R F V P B → sats R (F / (nf (length B)) ↦f fn) V P (f ∷ B)  
sats-to-sats P B R F V fn f h0 h1 h2 h3 g (or-lft h4) = 
  snd (good-to-holds-update-iff R F V (length B) fn g (h0 g _ h4)) (h3 g (or-lft h4))
sats-to-sats P B R F V fn f h0 h1 h2 h3 g (or-rgt (or-lft h4)) = 
  eq-elim (λ x → R , _ , V ⊢ x) (eq-symm h4) h2
sats-to-sats P B R F V fn f h0 h1 h2 h3 g (or-rgt (or-rgt h4)) = 
  snd (good-to-holds-update-iff R F V (length B) fn g (h1 g h4)) (h3 g (or-rgt h4))

sat-to-sat-to-unsat-to-unsat : ∀ {P0 P1 B0 B1} → 
  (sat P0 B0 → sat P1 B1) → unsat P1 B1 → unsat P0 B0
sat-to-sat-to-unsat-to-unsat {P0} {P1} {B0} {B1} h0 h1 = 
  or-elim (sat-or-unsat P0 B0) 
    (λ h2 → ⊥-elim (unsat-to-not-sat P1 B1 h1 (h0 h2))) 
    id

prsv-d : ∀ P B f g → good-prob P → good-bch B → f ∈ B → 
  (break-d (length B) f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-d P B f g hP hB hi hb = 
  sat-to-sat-to-unsat-to-unsat 
    ( ex-elim-3' 
        ( λ R F V (h0 , h1) → 
            ex-elim (prsv-d-aux R F V (length B) f g (hB f hi) hb (h1 f (or-rgt hi))) 
              λ d h2 → 
                R , 
                  F / (nf (length B)) ↦f (const-fn d) , 
                    V , h0 , sats-to-sats P B R F V (const-fn d) g hP hB h2 h1 ) )


-- prsv-d : ∀ P B f g → good-prob P → good-bch B → f ∈ B → 
--   (break-d (length B) f ≡ just g) → unsat P (g ∷ B) → unsat P B 
-- prsv-d P B f g hP hB hi hb hu = or-elim (sat-or-unsat P B)
--   ( λ h0 → ex-elim-3 h0 (λ R F V (h1 , h2) →
--       ex-elim (prsv-d-aux R F V (length B) f g (hB f hi) hb (h2 f (or-rgt hi))) λ d h3 → 
--         let F' = F / nf (length B) ↦f const-fn d in
--         ⊥-elim (unsat-to-not-sat _ _ hu (R , F' , V ,  h1 , λ h h4 → 
--           or-elim h4 
--             (λ h5 → and-rgt (good-to-holds-update-iff R F V (length B) _ h 
--               (hP h (length B) h5)) (h2 h (or-lft h5)))
--             ( or-elim' 
--               (λ h5 → eq-elim (λ x → R , F' , V ⊢ x) (eq-symm h5) h3) 
--               (λ h5 → and-rgt (good-to-holds-update-iff R F V (length B) _ h _) (h2 h (or-rgt h5))) ) ) ) ) ) 
--   id

prsv-n : ∀ P B g → (not (not g)) ∈ B → unsat P (g ∷ B) → unsat P B 
prsv-n P B g h1 h2 = prsv-implies P B (not (not g)) g h1 (λ R F V → dne) h2 

prsv-p : ∀ P B g → in-prob g P → unsat P (g ∷ B) → unsat P B 
prsv-p P B g h0 h1 R F V hR = 
  ex-elim (h1 R F V hR) 
    λ f (h2 , h3) → 
      f , 
      or-elim h2 or-lft 
        (or-elim' (λ h4 → or-lft (eq-elim (λ x → in-prob x P) (eq-symm h4) h0)) or-rgt) , 
      h3

prsv-s : ∀ P B g → unsat P (not g ∷ B) → unsat P (g ∷ B) → unsat P B 
prsv-s P B g h0 h1 R F V hR = 
  ex-elim (h0 R F V hR) 
    λ f0 (h2 , h3) → 
      ex-elim (h1 R F V hR) 
        λ f1 (h4 , h5) → 
          or-elim h2 
            (λ h6 → f0 , or-lft h6 , h3) 
            ( or-elim'
                ( λ h6 → 
                    or-elim h4 
                      (λ h7 → f1 , or-lft h7 , h5) 
                     ( or-elim' 
                          ( λ h9 → 
                              ex-falso { R , F , V ⊢ g } 
                                (dne (eq-elim (λ x → ¬ (R , F , V ⊢ x)) h6 h3)) 
                                (eq-elim (λ x → ¬ (R , F , V ⊢ x)) h9 h5) ) 
                          (λ h8 → f1 , or-rgt h8 , h5) ) ) 
                (λ h6 → f0 , or-rgt h6 , h3) ) 


standard-to-holds : Form → Set 
standard-to-holds f = ∀ R F V → standard R → R , F , V ⊢ f

standard-to-holds-refl : standard-to-holds refl-axiom
standard-to-holds-refl R F V hR d = and-rgt (hR d d) refl

standard-to-holds-symm : standard-to-holds symm-axiom
standard-to-holds-symm R F V hR d0 d1 h0 = 
  and-rgt (hR d1 d0) (eq-symm (and-lft (hR d0 d1) h0))

standard-to-holds-trans : standard-to-holds trans-axiom
standard-to-holds-trans R F V hR d0 d1 d2 h0 h1 = 
  and-rgt (hR d0 d2) (eq-trans d1 (and-lft (hR d0 d1) h0) (and-lft (hR d1 d2) h1))

-- mono-args-equal : Nat → VA → Set
-- mono-args-equal 0 _ = ⊤
-- mono-args-equal (suc k) V = (V (suc (k * 2)) ≡ V (k * 2)) ∧ (mono-args-equal k V)

mono-args-equal' : Nat → VA → Set
mono-args-equal' k V = ∀ m → m < k → V (suc (m * 2)) ≡ V (m * 2)

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

lt-to-lt-suc : ∀ k m → k < m → k < suc m
lt-to-lt-suc 0 m h0 = 0< m
lt-to-lt-suc (suc k) (suc m) (suc< k m h0) = 
  suc< k (suc m) (lt-to-lt-suc _ _ h0)

-- mono-args-equal-iff-mono-args-equal' : ∀ k V → 
--   (mono-args-equal k V ↔ mono-args-equal' k V)
-- mono-args-equal-iff-mono-args-equal' 0 V = top-iff (λ _ ())
-- mono-args-equal-iff-mono-args-equal' (suc k) V = 
--   ( λ h0 m h1 → 
--       or-elim (lt-suc-to-eq-or-lt m k h1) 
--         (λ h2 → eq-elim (λ x → V (suc (x * 2)) ≡ V (x * 2)) (eq-symm h2) (and-lft h0)) 
--         (and-lft (mono-args-equal-iff-mono-args-equal' k V) (and-rgt h0) m) ) , 
--   λ h0 → 
--     h0 k (lt-suc-self k) , 
--     and-rgt (mono-args-equal-iff-mono-args-equal' k V) 
--       λ m h1 → h0 m (lt-to-lt-suc _ _ h1)

from-mono-args-equal-suc : ∀ V k → 
  mono-args-equal' (suc k) V → mono-args-equal' k V 
from-mono-args-equal-suc V k h0 m h1 = h0 m (lt-to-lt-suc m k h1) 

from-mono-args-equal-0 : ∀ F V k → mono-args-equal' k V → 
  (terms-val F V (mono-args-lft k) ≡ terms-val F V (mono-args-rgt k)) 
from-mono-args-equal-0 F V 0 _ = refl
from-mono-args-equal-0 F V (suc k) h0 = 
  cong2 _∷_ (h0 k (lt-suc-self k)) 
    (from-mono-args-equal-0 F V k (from-mono-args-equal-suc V k h0)) 

from-mono-args-equal-1 : ∀ V k d → mono-args-equal' k V → 
  mono-args-equal' (suc k) ((V / 0 ↦ d) / 0 ↦ d) 
from-mono-args-equal-1 V k d h0 0 h1 = refl
from-mono-args-equal-1 V k d h0 (suc m) (suc< _ _ h1) = h0 m h1

holds-mono-fun : ∀ R F V k m f → standard R → 
  mono-args-equal' m V → mono-fun k m f → R , F , V ⊢ f 
holds-mono-fun R F V k m _ hR hE (mono-fun-fa k m f h0) d0 d1 h1 = 
  holds-mono-fun R F _ k (suc m) f hR 
    ( let h2 : d0 ≡ d1 
          h2 = (and-lft (hR d0 d1) h1) in 
      eq-elim (λ x → mono-args-equal' (suc m) ((V / 0 ↦ d0) / 0 ↦ x)) 
        h2 ((from-mono-args-equal-1 V m d0 hE)))
    h0
holds-mono-fun R F V k m _ hR hE (mono-fun-eq k m f _) = 
  and-rgt (hR _ _) (cong (F f) (from-mono-args-equal-0 F V m hE))

holds-mono-rel : ∀ R F V k m f → standard R → 
  mono-args-equal' m V → mono-rel k m f → R , F , V ⊢ f 
holds-mono-rel R F V k m _ hR hE (mono-rel-fa k m f h0) d0 d1 h1 = 
  holds-mono-rel R F _ k (suc m) f hR 
    ( let h2 : d0 ≡ d1 
          h2 = (and-lft (hR d0 d1) h1) in 
      eq-elim (λ x → mono-args-equal' (suc m) ((V / 0 ↦ d0) / 0 ↦ x)) 
        h2 (from-mono-args-equal-1 V m d0 hE) )
    h0
holds-mono-rel R F V k m _ hR hE (mono-rel-imp k m r _) h0 = 
  eq-elim (λ x → tr (R r x)) (from-mono-args-equal-0 _ _ _ hE) h0

standard-to-holds-mono-rel : ∀ k f → mono-rel k 0 f → standard-to-holds f
standard-to-holds-mono-rel k f h0 R F V hR = holds-mono-rel R F V k 0 f hR (λ _ ()) h0

standard-to-holds-mono-fun : ∀ k f → mono-fun k 0 f → standard-to-holds f
standard-to-holds-mono-fun k f h0 R F V hR = holds-mono-fun R F V k 0 f hR (λ _ ()) h0

standard-to-holds-top : standard-to-holds (cst true)
standard-to-holds-top R F V hR = tt

standard-to-holds-not-bot : standard-to-holds (not (cst false))
standard-to-holds-not-bot R F V hR = id

standard-to-unsat : ∀ {P B f} → standard-to-holds f → unsat P (f ∷ B) → unsat P B
standard-to-unsat {_} {_} {f} h0 h1 R F V hR = 
  ex-elim (h1 R F V hR) 
    λ g (h2 , h3) → 
      g , 
      or-elim h2 or-lft 
        ( or-elim' 
            ( λ h4 → 
                ex-falso (eq-elim (λ x → R , F , V ⊢ x) (eq-symm h4) (h0 R F V hR)) 
                  h3 ) 
            or-rgt ) , 
      h3

prsv-t : ∀ P B g → good-prob P → good-bch B → jst (length B) g → unsat P (g ∷ B) → unsat P B 
prsv-t P B _ _ _ (jst-top _)           = standard-to-unsat standard-to-holds-top
prsv-t P B _ _ _ (jst-not-bot _)       = standard-to-unsat standard-to-holds-not-bot
prsv-t P B _ _ _ (jst-refl _)          = standard-to-unsat standard-to-holds-refl
prsv-t P B _ _ _ (jst-symm k)          = standard-to-unsat standard-to-holds-symm
prsv-t P B _ _ _ (jst-trans k)         = standard-to-unsat standard-to-holds-trans
prsv-t P B _ _ _ (jst-fun k f h0)      = standard-to-unsat (standard-to-holds-mono-fun k f h0)
prsv-t P B _ _ _ (jst-rel k f h0)      = standard-to-unsat (standard-to-holds-mono-rel k f h0)
prsv-t P B _ hP hB (jst-choice k f h0)   = 
  sat-to-sat-to-unsat-to-unsat 
    ( ex-elim-3' 
        λ R F V (h1 , h2) → 
          ex-elim (prsv-t-choice R F (length B) 0 f h0) 
            λ fn h3 → 
              R , F / nf (length B) ↦f fn , V , h1 , sats-to-sats P B R F V fn f hP hB  (h3 V) h2 ) 
prsv-t P B _ hP hB (jst-pred-def k f h0) = 
  sat-to-sat-to-unsat-to-unsat (ex-elim-3' λ R F V (h1 , h2 ) → {!   !})

prsv-good-b : ∀ f g h k → (break-b f ≡ just (g , h)) → good-form k f → 
  (good-form k g ∧ good-form k h)
prsv-good-b (bct or f0 f1) g h k h0 h1 =
  ( (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) (and-lft h1)) , 
    (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (and-rgt h1)) )
prsv-good-b (bct imp f0 f1) g h k h0 h1 = 
  ( (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) (and-lft  h1)) , 
    (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (and-rgt h1)) )
prsv-good-b (not (bct and f0 f1)) g h k h0 h1 = 
  (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) (and-lft  h1)) , 
  (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (and-rgt h1)) 
prsv-good-b (not (bct iff f0 f1)) g h k h0 h1 = 
  (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) h1) , 
  (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (and-symm h1)) 

good-subst-termoid : ∀ {b} s (t : Termoid b) k m → good-term k s → 
  good-termoid k t → good-termoid k (subst-termoid m s t)
good-subst-termoid {true} _ nil _ _ _ _ = tt
good-subst-termoid {true} s (cons t ts) k m h0 h1 = 
  (good-subst-termoid s _ _ _ h0 (and-lft h1)) ,
  (good-subst-termoid s _ _ _ h0 (and-rgt h1)) 
good-subst-termoid {false} s (var n) k m h0 h1 = 
  tri-elim m n (good-termoid k) (\ _ → tt) (\ _ → h0) (\ _ → tt)
good-subst-termoid {false} s (fun f ts) k m h0 h1 = 
  (and-lft h1) , (good-subst-termoid _ ts k m h0 (and-rgt h1))

good-subst-terms : ∀ t ts k m → good-term k t → 
  good-terms k ts → good-terms k (subst-terms m t ts)
good-subst-terms = good-subst-termoid 

good-incr-var : ∀ {b} k (t : Termoid b) → good-termoid k t → good-termoid k (incr-var t)
good-incr-var _ nil _ = tt
good-incr-var k (cons t ts) h = 
  (good-incr-var _ t (and-lft h)) , (good-incr-var _ ts (and-rgt h))
good-incr-var k (var _) _ = tt
good-incr-var k (fun f ts) h = 
  and-lft h , (good-incr-var _ ts (and-rgt h))

good-subst-form : ∀ t f k m → good-term k t → good-form k f → good-form k (subst-form m t f)
good-subst-form t (cst _) _ _ _ _ = tt
good-subst-form t (rel r ts) k m h0 h1 = 
  and-lft h1 , good-subst-terms t ts k m h0 (and-rgt h1)
good-subst-form t (not f) = good-subst-form t f
good-subst-form t (bct _ f g) k m h0 h1 = 
  (good-subst-form t f k m h0 (and-lft h1)) , (good-subst-form t g k m h0 (and-rgt h1))
good-subst-form t (qtf _ f) k m h0 h1 = 
  good-subst-form (incr-var t) f k (suc m) (good-incr-var _ _ h0) h1

prsv-good-d : ∀ f g k → good-form k f → (break-d k f ≡ just g) → good-form (suc k) g
prsv-good-d f g k = {!   !}

prsv-good-c : ∀ t f g k → good-term k t → good-form k f → (break-c t f ≡ just g) → good-form k g
prsv-good-c t (qtf false f) g k h0 h1 h2 = 
  eq-elim (good-form k) (just-inj h2) (good-subst-form t f _ _ h0 h1)
prsv-good-c t (not (qtf true f)) g k h0 h1 h2 = 
  eq-elim (good-form k) (just-inj h2) (good-subst-form t f k 0 h0 h1) 

prsv-good-a : ∀ b f g k → (break-a b f ≡ just g) → good-form k f → good-form k g
prsv-good-a true  (bct and f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-lft h1)
prsv-good-a false (bct and f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-rgt h1)
prsv-good-a true  (bct iff f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) h1 --h1
prsv-good-a false (bct iff f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-symm h1)
prsv-good-a true  (not (bct or f0 f1))  g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-lft h1) -- \ m h2 → h1 m (or-lft h2)
prsv-good-a false (not (bct or f0 f1))  g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-rgt h1) -- \ m h2 → h1 m (or-rgt h2)
prsv-good-a true  (not (bct imp f0 f1)) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-lft h1) -- \ m h2 → h1 m (or-lft h2)
prsv-good-a false (not (bct imp f0 f1)) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-rgt h1) -- \ m h2 → h1 m (or-rgt h2)

good-bch-t : ∀ B g → jst (length B) g → good-bch B → good-bch (g ∷ B)
good-bch-t B g h0 h1 = {!   !}

good-bch-p : ∀ P B g → good-prob P →  good-bch B → in-prob g P → good-bch (g ∷ B)
good-bch-p P B g h0 h1 h2 = good-bch-cons g B (h0 _ _ h2) h1

good-bch-n : ∀ B g → (not (not g)) ∈ B → good-bch B → good-bch (g ∷ B)
good-bch-n B g h0 h1 = good-bch-cons g B (good-form-suc _ (not (not g)) (h1 (not (not g)) h0)) h1

good-bch-a : ∀ B b f g → f ∈ B → (break-a b f ≡ just g) → good-bch B → good-bch (g ∷ B)
good-bch-a B b f g h0 h1 h2 = good-bch-cons _ _ 
  (good-form-suc _ g (prsv-good-a _ _ _ _ h1 (h2 f h0))) h2 

good-bch-b : ∀ B f g h → f ∈ B → (break-b f ≡ just (g , h)) → 
  good-bch B → (good-bch (g ∷ B) ∧ good-bch (h ∷ B))
good-bch-b B f g h h0 h1 h2 = 
  ( good-bch-cons _ _ (good-form-suc _ g (and-lft  (prsv-good-b _ _ _ _ h1 (h2 f h0)))) h2 , 
    good-bch-cons _ _ (good-form-suc _ h (and-rgt (prsv-good-b _ _ _ _ h1 (h2 f h0)))) h2 )

good-bch-c : ∀ B t f g → good-term (suc (length B)) t → 
  f ∈ B → (break-c t f ≡ just g) → good-bch B → good-bch (g ∷ B) 
good-bch-c B t f g h0 h1 h2 h3 = good-bch-cons _ _ 
  (prsv-good-c t f g (suc (length B)) h0 (good-form-suc _ f (h3 _ h1)) h2)  h3

good-bch-d : ∀ B f g → f ∈ B → (break-d (length B) f ≡ just g) → good-bch B → good-bch (g ∷ B) 
good-bch-d B f g h0 h1 h2 = good-bch-cons g B (prsv-good-d f g (length B) (h2 f h0) h1) h2

is-just : ∀ {A : Set} → Maybe A → Set
is-just nothing = ⊥
is-just (just _) = ⊤

from-is-just-bind : ∀ {A} {B} (f : Read A) (g : A → Read B) cs → 
    is-just ((f >>= g) cs) → 
    ∃ (\ x → ∃ (\ cs' → (f cs ≡ just (x , cs')) ∧ (is-just (g x cs'))))
from-is-just-bind f g cs with f cs 
... | nothing = ⊥-elim
... | (just (x , cs')) = \ h0 → (x , (cs' , (refl , h0)))

use-is-just-bind : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 → 
  is-just ((f >>= g) cs0) → (∀ a cs1 → (f cs0 ≡ just (a , cs1)) → (is-just (g a cs1)) → C) → C
use-is-just-bind f g cs h0 h1 = 
  ex-elim-2 (from-is-just-bind f g cs h0) λ a cs' (h2 , h3) → h1 a cs' h2 h3

use-is-just-bind' : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 → 
  (∀ a cs1 → (f cs0 ≡ just (a , cs1)) → (is-just (g a cs1)) → C) → is-just ((f >>= g) cs0) → C 
use-is-just-bind' f g cs h0 h1 = use-is-just-bind f g cs h1 h0 
    
ends : ∀ {A : Set} → Read A → Set
ends r = ∃ λ cs → is-just (r cs)

ends-num : ∀ {A : Set} → (Nat → Read A) → Set
ends-num r = ∃ λ k → ends (r k)

passes : ∀ {A : Set} → Read A → A → Set
passes r a = ∃ λ cs0 → ∃ λ cs1 → (r cs0) ≡ just (a , cs1)

passes-num : ∀ {A : Set} → (Nat → Read A) → A → Set
passes-num r a = ∃ λ k → passes (r k) a

use-seq-eq-just : ∀ {A B C : Set} (r : Read A) (s : Read B) cs0 csf b → 
  ((r >> s) cs0) ≡ just (b , csf) → 
  (∀ a cs1 → r cs0 ≡ just (a , cs1) → (s cs1 ≡ just (b , csf)) → C) → C
use-seq-eq-just r s cs0 csf b h0 h1 with (r cs0)
... | just (a , cs1) = h1 a cs1 refl h0

use-is-just-seq : ∀ {A B C : Set} (r : Read A) (s : Read B) (cs) → 
  is-just ((r >> s) cs) → (∀ a cs' → r cs ≡ just (a , cs') → (is-just (s cs')) → C) → C
use-is-just-seq r s cs h0 h1 with (r cs) 
... | just (a , cs') = h1 a cs' refl h0 

use-is-just-seq' : ∀ {A B C : Set} (r : Read A) (s : Read B) (cs) → 
  (∀ a cs' → r cs ≡ just (a , cs') → (is-just (s cs')) → C) → 
  is-just ((r >> s) cs) → C
use-is-just-seq' r s cs h0 h1 = use-is-just-seq r s cs h1 h0 

eq-just-to-is-just : ∀ {A} {m} {a : A} → m ≡ just a → is-just m 
eq-just-to-is-just {_} {just _}  _ = tt

elim-ends-seq : ∀ {A B C : Set} (r : Read A) (s : Read B) → 
  (ends r → ends s → C) → ends (r >> s) → C
elim-ends-seq r s h0 = ex-elim' λ cs0 → 
  use-is-just-seq' r s cs0 λ a cs1 h1 h2 → 
    h0 (cs0 , eq-just-to-is-just  h1) (cs1 , h2) 

intro-verify : ∀ (Q : Maybe (⊤ × Chars) → Set) P B k c cs → 
  ( Q ( ( do
    f ← verify-a B 
    verify P (f ∷ B) k ) cs ) ) → 
  ( Q ( ( do
     (f , g) ← verify-b B 
     verify P (f ∷ B) k
     verify P (g ∷ B) k ) cs ) ) →  
  ( Q ( ( do
    f ← verify-c B k 
    verify P (f ∷ B) k ) cs ) ) → 
  ( Q ( ( do
    f ← verify-d B 
    verify P (f ∷ B) k ) cs ) ) →  
  ( Q ( ( do
    f ← verify-n B 
    verify P (f ∷ B) k ) cs ) ) → 
  ( Q ( ( do
    f ← verify-p P B 
    verify P (f ∷ B) k ) cs ) ) →  
  ( Q ( ( do
    f ← verify-s B k 
    verify P (not f ∷ B) k 
    verify P (f ∷ B) k ) cs ) ) →  
  ( Q ( ( do
    f ← verify-t B k 
    verify P (f ∷ B) k ) cs ) ) → 
  Q ( verify-x B cs ) → 
  Q nothing → 
  Q (verify P B (suc k) (c ∷ cs))
intro-verify Q P B k c cs ha hb hc hd hn hp hs ht hx h0 =  
  intro-ite {(Read ⊤)} {_} {_} (c ==c 'A') (λ x → (Q (x cs))) ha (
    intro-ite {(Read ⊤)} {_} {_} (c ==c 'B') (λ x → (Q (x cs))) hb (
      intro-ite {(Read ⊤)} {_} {_} (c ==c 'C') (λ x → (Q (x cs))) hc (
        intro-ite {(Read ⊤)} {_} {_} (c ==c 'D') (λ x → (Q (x cs))) hd (
          intro-ite {(Read ⊤)} {_} {_} (c ==c 'N') (λ x → (Q (x cs))) hn (
            intro-ite {(Read ⊤)} {_} {_} (c ==c 'P') (λ x → (Q (x cs))) hp (
              intro-ite {(Read ⊤)} {_} {_} (c ==c 'S') (λ x → (Q (x cs))) hs (
                intro-ite {(Read ⊤)} {_} {_} (c ==c 'T') (λ x → (Q (x cs))) ht (
                  intro-ite {(Read ⊤)} {_} {_} (c ==c 'X') (λ x → (Q (x cs))) hx h0
                )
              )
            )
          )
        )
      )
    )
  )

elim-ends-verify : ∀ P B k C → 
  (∀ f → passes (verify-a B) f → ends (verify P (f ∷ B) k) → C) →   
  ( ∀ f g → passes (verify-b B) (f , g) → 
    ends (verify P (f ∷ B) k) → ends (verify P (g ∷ B) k) → C) → 
  (∀ f → passes-num (verify-c B) f → ends (verify P (f ∷ B) k) → C) →  
  (∀ f → passes (verify-d B) f → ends (verify P (f ∷ B) k) → C) → 
  (∀ f → passes (verify-n B) f → ends (verify P (f ∷ B) k) → C) → 
  (∀ f → passes (verify-p P B) f → ends (verify P (f ∷ B) k) → C) →  
  ( ∀ f → passes-num (verify-s B) f → ends (verify P (not f ∷ B) k) → ends (verify P (f ∷ B) k) → C) → 
  (∀ f → passes-num (verify-t B) f → ends (verify P (f ∷ B) k) → C) →  
  (ends (verify-x B) → C) → 
  ends (verify P B (suc k)) → C
elim-ends-verify P B k C ha hb hc hd hn hp hs ht hx (c ∷ cs0 , hv) =
  intro-verify (λ x → is-just x → C) P B k c cs0 
    (use-is-just-bind' (verify-a B) _ cs0 λ f cs1 h0 h1 → ha f (cs0 , cs1 , h0) (cs1 , h1)) --(... λ f cs1 h0 h1 → ha f (cs0 , cs1 , h0) (k , cs1 , h1)) 
    ( use-is-just-bind' (verify-b B) _ cs0 
        λ (f , g) cs1 h0 h1 → 
          elim-ends-seq (verify P (f ∷ B) k) (verify P (g ∷ B) k) 
            (λ h2 h3 → hb f g (cs0 , cs1 , h0) h2 h3) (cs1 , h1) ) 
    ( use-is-just-bind' (verify-c B k) _ cs0 
        λ f cs1 h0 h1 → hc f (k , cs0 , cs1 , h0) (cs1 , h1) ) 
    ( use-is-just-bind' (verify-d B) _ cs0 
        λ f cs1 h0 h1 → hd f (cs0 , cs1 , h0) (cs1 , h1) ) 
    ( use-is-just-bind' (verify-n B) _ cs0 
        λ f cs1 h0 h1 → hn f (cs0 , cs1 , h0) (cs1 , h1) ) 
    ( use-is-just-bind' (verify-p P B) _ cs0 
        λ f cs1 h0 h1 → hp f (cs0 , cs1 , h0) (cs1 , h1) ) 
    ( use-is-just-bind' (verify-s B k) _ cs0 
        λ f cs1 h0 h1 → 
          elim-ends-seq (verify P (not f ∷ B) k) (verify P (f ∷ B) k) 
            (λ h2 h3 → hs f (k , cs0 , cs1 , h0) h2 h3) 
            (cs1 , h1) )
    ( use-is-just-bind' (verify-t B k) _ cs0 
        λ f cs1 h0 h1 → ht f (k , cs0 , cs1 , h0) (cs1 , h1) ) 
    (λ h0 → hx (cs0 , h0)) 
    ⊥-elim 
    hv
  -- elim-ite' {Read ⊤} (λ x → is-just (x cs0)) (c ==c 'A') _ _ hv 
  --   ( use-is-just-bind' (verify-a B) _ cs0 λ f cs1 h0 h1 → ha f (cs0 , cs1 , h0) (k , cs1 , h1) ) 
  --   ( 
  --     elim-ite {Read ⊤} (λ x → is-just (x cs0)) (c ==c 'B') _ _ 
  --       ( use-is-just-bind' (verify-b B) _ cs0 λ (f , g) cs1 h0 h1 → 
  --         elim-ends-seq (verify P (f ∷ B) k) (verify P (g ∷ B) k) 
  --           (λ h2 h3 → hb f g (cs0 , cs1 , h0) (k , h2) (k , h3)) 
  --           (cs1 , h1) ) 
  --       ( 
  --         elim-ite {Read ⊤} (λ x → is-just (x cs0)) (c ==c 'C') _ _ 
  --           {!   !} 
  --           {!   !}
  --       ) 
  --   ) 
  --   
  --   




    --( elim-ite {Read ⊤} (λ x → is-just (x cs0)) (c ==c 'B') _ _ {!   !} {!   !} {!   !}) 

  --   (use-is-just-bind' (verify-a B) _ cs0 λ f cs1 h0 h1 → or-lft (f , (cs0 , cs1 , h0) , k , cs1 , h1)) --(use-is-just-bind' _ {!   !} {!   !} {!   !})
  --   λ hb → elim-ite {Read ⊤} (λ x → is-just (x cs0)) (c ==c 'B') _ _ hb 
  --     (use-is-just-bind' (verify-b B) _ cs0 λ (f , g) cs1 h0 h1 → {!   !}) 
  --     {!   !}


--   ( Q ( do
--      (f , g) ← verify-b B 
--      verify P (f ∷ B) k
--      verify P (g ∷ B) k ) ) →  
--   ( Q ( do
--     f ← verify-c B k 
--     verify P (f ∷ B) k ) ) → 
--   ( Q ( do
--     f ← verify-d B 
--     verify P (f ∷ B) k ) ) →  
--   ( Q ( do
--     f ← verify-n B 
--     verify P (f ∷ B) k ) ) → 
--   ( Q ( do
--     f ← verify-p P B 
--     verify P (f ∷ B) k ) ) →  
--   ( Q ( do
--     f ← verify-s B k 
--     verify P (not f ∷ B) k 
--     verify P (f ∷ B) k ) ) →  
--   ( Q ( do
--     f ← verify-t B k 
--     verify P (f ∷ B) k ) ) → 
--   Q (verify-x B) → 
--   Q fail → 
--   Q (verify P B (suc k))
-- intro-verify' Q P B k ha hb hc hd hn hp hs ht hx h0 = {!   !} 
--   intro-ite {(Read ⊤)} {_} {_} (c ==c 'A') (λ x → (Q (x cs))) ha (
--     intro-ite {(Read ⊤)} {_} {_} (c ==c 'B') (λ x → (Q (x cs))) hb (
--       intro-ite {(Read ⊤)} {_} {_} (c ==c 'C') (λ x → (Q (x cs))) hc (
--         intro-ite {(Read ⊤)} {_} {_} (c ==c 'D') (λ x → (Q (x cs))) hd (
--           intro-ite {(Read ⊤)} {_} {_} (c ==c 'N') (λ x → (Q (x cs))) hn (
--             intro-ite {(Read ⊤)} {_} {_} (c ==c 'P') (λ x → (Q (x cs))) hp (
--               intro-ite {(Read ⊤)} {_} {_} (c ==c 'S') (λ x → (Q (x cs))) hs (
--                 intro-ite {(Read ⊤)} {_} {_} (c ==c 'T') (λ x → (Q (x cs))) ht (
--                   intro-ite {(Read ⊤)} {_} {_} (c ==c 'X') (λ x → (Q (x cs))) hx h0
--                 )
--               )
--             )
--           )
--         )
--       )
--     )
--   )

from-eq-just : ∀ {A} {B} (f : Read A) (g : A → Read B) {cs0} {cs1} {b} → 
   ((f >>= g) cs0) ≡ just (b , cs1) → 
   ∃ \ a → ∃ \ cs → (f cs0 ≡ just (a , cs)) ∧ (g a cs ≡ just (b , cs1))
from-eq-just f g {cs0} h with f cs0
... | (just (a , cs)) = a , cs , refl , h

use-bind-eq-just : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 cs1 b → 
  ((f >>= g) cs0) ≡ just (b , cs1) → 
  (∀ a cs → (f cs0 ≡ just (a , cs)) → (g a cs ≡ just (b , cs1)) → C) → C
use-bind-eq-just f g cs0 cs1 b h0 h1 = ex-elim (from-eq-just f g h0) 
  \ a h2 → ex-elim h2 (λ cs h3 → h1 a cs (and-lft h3) (and-rgt h3))

use-obind-eq-just : ∀ {A B C : Set} (f : Maybe A) (g : A → Maybe B) (b : B) → 
  (f o>= g) ≡ just b → (∀ a → f ≡ just a → g a ≡ just b → C) → C 
use-obind-eq-just (just a) g b h0 h1 = h1 a refl h0

from-obind-eq-just : ∀ {A B : Set} (f : Maybe A) (g : A → Maybe B) (b : B) → 
  (f o>= g) ≡ just b → ∃ \ a → ((f ≡ just a) ∧ (g a ≡ just b))
from-obind-eq-just nothing _ _  () 
from-obind-eq-just (just a) g b h0 = (a , (refl , h0))

from-lift-read-eq-just : ∀ {A} {f : Maybe A} {a cs0 cs1} → 
  ((lift-read f) cs0 ≡ just (a , cs1)) → f ≡ just a
-- from-lift-read-eq-just nothing _ _ _ ()
from-lift-read-eq-just {_} {just a0} {_} {_} {_} h0 = cong just (prod-inj-lft (just-inj h0))

from-nth-eq-just : ∀ {A : Set} k l (x : A) → nth k l ≡ just x → x ∈ l
from-nth-eq-just 0 (y ∷ _) x = \ h0 → or-lft (eq-symm (just-inj h0))
from-nth-eq-just (suc m) (_ ∷ ys) x = \ h0 → or-rgt (from-nth-eq-just m ys x h0)

from-get-bch-eq-just : ∀ {B} {m} {f} → get-bch B m ≡ just f → f ∈ B
from-get-bch-eq-just {B} {m} {f} h0 =  
  ex-elim 
    (from-obind-eq-just 
      (rev-index (length B) m) 
      (\ n → nth n B) f h0) 
      \ k h1 → from-nth-eq-just k _ _ (and-rgt h1)

from-lift-read-get-bch : ∀ {A : Set} B m (d : Form → Maybe A) f cs0 cs1 →  
  lift-read (get-bch B m o>= d) cs0 ≡ just (f , cs1) → 
    ∃ \ g → ((g ∈ B) ∧ (d g ≡ just f))
from-lift-read-get-bch B m d f cs0 cs1 h0 = 
  let h1 : ∃ \ g → ((get-bch B m ≡ just g) ∧ (d g ≡ just f))
      h1 =  from-obind-eq-just _ d f (from-lift-read-eq-just h0) 
  in ex-elim h1 \ g h2 → 
    (g , (from-get-bch-eq-just (and-lft h2) , and-rgt h2))


correct-aux : ∀ {f g : Read ⊤} P B c0 c1 cs
  (h0 : is-just (f cs) → unsat P B)  
  (h1 : is-just (g cs) → unsat P B)  
  → -------------------------------
  is-just ((if c0 ==c c1 then f else g) cs) → unsat P B 
correct-aux P B c0 c1 cs = 
  intro-ite (c0 ==c c1) (λ (x : Read ⊤) → is-just (x cs) → unsat P B) 

-- use-get-bch : 
--   {X : Set} 
--   {Y : Set}
--   (B : Bch)
--   (k : Nat)
--   (m : Form → Maybe X)
--   (r : X → Read ⊤)
--   (cs0 : Chars)
--   (h0 : is-just (((lift-read (get-bch B k o>= m)) >>= r) cs0)) 
--   (h1 : ∀ f x cs → (f ∈ B) → (m f ≡ just x) → is-just ((r x) cs) → Y)
--   → ----------------------
--   Y
-- use-get-bch B k m r cs0 h0 h1 = 
--   use-is-just-bind (lift-read (get-bch B k o>= m)) r cs0 h0 λ x cs1 h2 h3 → 
--     use-obind-eq-just (get-bch B k) m x (from-lift-read-eq-just h2) λ f h4 h5 → 
--       h1 f x cs1 (from-get-bch-eq-just h4) h5 h3 
-- 
from-lift-read-bind-eq : ∀ {A} B k (m : Form → Maybe A) cs0 csf (a : A) → 
  lift-read (get-bch B k o>= m) cs0 ≡ just (a , csf) → 
  ∃ λ f → ((f ∈ B) ∧ (m f ≡ just a))
from-lift-read-bind-eq B k m cs0 csf a h0 =
  ex-elim (from-obind-eq-just (get-bch B k) m a (from-lift-read-eq-just h0)) 
    λ f h1 → (f , from-get-bch-eq-just (and-lft h1) , and-rgt h1)

from-pass-if-seq-eq-just : ∀ {A} b (r : Read A) cs0 csf a → 
  (pass-if b >> r) cs0 ≡ just (a , csf) → (tr b ∧ (r cs0 ≡ just (a , csf)))
from-pass-if-seq-eq-just true r cs0 csf a h0 = tt , h0 

from-passes-verify-a : ∀ B f → passes (verify-a B) f → 
  ∃ λ b → ∃ λ g → ((g ∈ B) ∧ (break-a b g ≡ just f))
from-passes-verify-a B f (cs0 , (cs1 , h0)) =
  use-bind-eq-just read-nat _ cs0 cs1 f h0 λ k cs h1 h2 → 
    use-bind-eq-just read-bool _ cs cs1 f h2 λ b cs' h3 h4 → 
      b , from-lift-read-bind-eq B k _ _ _ f h4

from-verify-a-eq-just : ∀ B cs0 cs1 g → verify-a B cs0 ≡ just (g , cs1) → 
  ∃ \ b → ∃ \ f → ((f ∈ B) ∧ (break-a b f ≡ just g))
from-verify-a-eq-just B cs0 cs1 g h0 = 
  use-bind-eq-just read-nat _ cs0 cs1 g h0 λ k cs h1 h2 → 
    use-bind-eq-just read-bool _ cs cs1 g h2 λ b cs' h3 h4 → 
      b , from-lift-read-bind-eq B k _ _ _ g h4

from-passes-verify-b : ∀ B f g → passes (verify-b B) (f , g) → 
  ∃ λ h → (h ∈ B) ∧ (break-b h ≡ just (f , g))
from-passes-verify-b B f g (cs0 , cs1 , h0) = 
  use-bind-eq-just read-nat _ cs0 cs1 (f , g) h0 λ k cs1 h1 h2 → 
    from-lift-read-bind-eq B k _ _ _ (f , g) h2

from-verify-b-eq-just : ∀ B cs0 cs1 gh → verify-b B cs0 ≡ just (gh , cs1) → 
  ∃ λ f → ((f ∈ B) ∧ (break-b f ≡ just gh))
from-verify-b-eq-just B cs0 csf gh h0 = 
  use-bind-eq-just read-nat _ cs0 csf gh h0 λ k cs1 h1 h2 → 
    from-lift-read-bind-eq B k _ _ _ gh h2

from-passes-num-verify-c : ∀ B g → passes-num (verify-c B) g →
  ∃ λ t → ∃ λ f → (good-term (suc (length B)) t) ∧ (f ∈ B) ∧ (break-c t f ≡ just g)
from-passes-num-verify-c B g (k , cs0 , csf , h0) =
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    use-bind-eq-just (read-term k) _ cs1 csf g h1  λ t cs2 h2 h3 → 
      let (h4 , h5) = from-pass-if-seq-eq-just (chk-good-term (suc (length B)) t) _ cs2 csf g h3 
      in ex-elim (from-lift-read-bind-eq B _ _ cs2 csf g h5) λ f (h6 , h7) → 
      t , f , checks-good (suc (length B)) t h4 , h6 , h7 

from-verify-c-eq-just : ∀ B k cs0 csf g → (verify-c B k cs0 ≡ just (g , csf)) →
  ∃ λ t → ∃ λ f → ((good-term (suc (length B)) t) ∧ ((f ∈ B) ∧ (break-c t f ≡ just g)))
from-verify-c-eq-just B k cs0 csf g h0  = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    use-bind-eq-just (read-term k) _ cs1 csf g h1  λ t cs2 h2 h3 → 
      let (h4 , h5) = from-pass-if-seq-eq-just (chk-good-term (suc (length B)) t) _ cs2 csf g h3 
      in ex-elim (from-lift-read-bind-eq B _ _ cs2 csf g h5) λ f (h6 , h7) → 
      t , f , checks-good (suc (length B)) t h4 , h6 , h7 

from-passes-verify-d : ∀ B g → passes (verify-d B) g → 
  ∃ λ f → (f ∈ B) ∧ (break-d (length B) f ≡ just g)
from-passes-verify-d B g (cs0 , csf , h0) =
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → f , h2 , h3

from-verify-d-eq-just : ∀ B cs0 csf g → (verify-d B cs0 ≡ just (g , csf)) → 
  ∃ λ f → ((f ∈ B) ∧ (break-d (length B) f ≡ just g))
from-verify-d-eq-just B cs0 csf g h0 = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → f , h2 , h3

from-passes-num-verify-s : ∀ B g → passes-num (verify-s B) g → good-form (suc (length B)) g 
from-passes-num-verify-s B g (k , cs0 , csf , h0) = 
  use-bind-eq-just (read-form k) _ cs0 csf g h0 
    λ f cs1 h1 h2 → 
      let (h3 , h4) = from-pass-if-seq-eq-just (chk-good-form _ f) _ cs1 csf _ h2 in 
      let h5 = checks-good-form _ f h3 in 
      eq-elim _ (prod-inj-lft (just-inj h4)) h5

from-passes-num-verify-t : ∀ B g → passes-num (verify-t B) g → jst (length B) g 
from-passes-num-verify-t = {!   !}

from-ends-verify-x : ∀ B → ends (verify-x B) → ∃ λ f → (f ∈ B) ∧ ((not f) ∈ B)
from-ends-verify-x = {!   !}

in-prob-cons : ∀ f P p → in-prob f P → in-prob f (p ∷ P) 
in-prob-cons f P p = ex-elim' λ nm h0 → (nm , or-rgt h0)

from-pass-eq-lft : ∀ {A : Set} (a0 a1 : A) cs0 cs1 → pass a0 cs0 ≡ just (a1 , cs1) → a0 ≡ a1
from-pass-eq-lft a0 a1 cs0 cs1 h0 = prod-inj-lft (just-inj h0) 

from-get-from-prob-eq : ∀ P nm0 cs0 cs1 f → 
  get-from-prob P nm0 cs0 ≡ just (f , cs1) → (in-prob f P) 
from-get-from-prob-eq ((nm1 , g) ∷ P) nm0 cs0 cs1 f = 
  intro-ite {_} {pass g} (eq-chars nm1 nm0)
    (λ x → x cs0 ≡ just (f , cs1) → in-prob f ((nm1 , g) ∷ P)) 
    ( λ h0 → eq-elim (λ x → in-prob x ((nm1 , g) ∷ P)) 
      (prod-inj-lft (just-inj h0)) ((nm1 , or-lft refl)) ) 
    λ h0 → in-prob-cons _ _ _ (from-get-from-prob-eq P nm0 cs0 cs1 f h0)

from-passes-verify-p : ∀ P B g → passes (verify-p P B) g → 
  in-prob g P ∧ good-form (suc (length B)) g
from-passes-verify-p P B g (cs0 , csf , h0) =
  use-bind-eq-just read-chars _ cs0 csf g h0 λ nm cs1 h1 h2 → 
    use-bind-eq-just (get-from-prob P nm) _ cs1 csf g h2 λ f cs2 h3 h4 → 
    let h5 = from-get-from-prob-eq P _ _ _ _ h3 in 
    let (h6 , h7) = from-pass-if-seq-eq-just (chk-good-form (suc (length B)) f) _ cs2 csf g h4 in 
    let h8 = from-pass-eq-lft _ _ _ _ h7 in 
    eq-elim (λ x → in-prob x P ∧ good-form (suc (length B)) x) h8 (h5 , checks-good-form _ f h6)

from-verify-p-eq-just : ∀ P B cs0 csf g → (verify-p P B cs0 ≡ just (g , csf)) → 
  (in-prob g P ∧ good-form (suc (length B)) g)
from-verify-p-eq-just P B cs0 csf g h0 = 
  use-bind-eq-just read-chars _ cs0 csf g h0 λ nm cs1 h1 h2 → 
    use-bind-eq-just (get-from-prob P nm) _ cs1 csf g h2 λ f cs2 h3 h4 → 
    let h5 = from-get-from-prob-eq P _ _ _ _ h3 in 
    let (h6 , h7) = from-pass-if-seq-eq-just (chk-good-form (suc (length B)) f) _ cs2 csf g h4 in 
    let h8 = from-pass-eq-lft _ _ _ _ h7 in 
    eq-elim (λ x → in-prob x P ∧ good-form (suc (length B)) x) h8 (h5 , checks-good-form _ f h6)

from-passes-verify-n : ∀ B g → passes (verify-n B) g → (not (not g)) ∈ B
from-passes-verify-n B g (cs0 , csf , h0) = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → 
     eq-elim (λ x → x ∈ B) (from-break-n-eq-just f g h3) h2

from-verify-n-eq-just : ∀ B cs0 csf g → (verify-n B cs0 ≡ just (g , csf)) → (not (not g)) ∈ B
from-verify-n-eq-just B cs0 csf g h0 = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → 
      eq-elim (λ x → x ∈ B) (from-break-n-eq-just f g h3) h2
    
    {-
correct-core : ∀ P B k → good-prob P → good-bch B → ends (verify P B k) → unsat P B
correct-core P B (suc k) hP hB = elim-ends-verify P B k (unsat P B)
  ( λ g h0 h1 → 
      ex-elim-2 (from-passes-verify-a B g h0) 
        λ b f (h2 , h3) →  
          prsv-a P B b f g h2 h3 (correct-core P _ k hP (good-bch-a B b f g h2 h3 hB) h1) ) 
  ( λ g h h0 h1 h2 → 
      ex-elim (from-passes-verify-b B g h h0) 
        λ f (h3 , h4) →
          let (h5 , h6) = good-bch-b B f g h h3 h4 hB in  
          prsv-b P B f g h h3 h4 (correct-core P _ k hP h5 h1) (correct-core P _ k hP h6 h2) ) 
  ( λ g h0 h1 → ex-elim-2 (from-passes-num-verify-c B g h0) λ t f (h2 , h3 , h4) → 
    prsv-c P B t f g h3 h4 (correct-core P _ k hP (good-bch-c B t f g h2 h3 h4 hB) h1) ) 
  ( λ g h0 h1 → ex-elim (from-passes-verify-d B g h0) λ f (h2 , h3) → 
    prsv-d P B f g hP hB h2 h3 (correct-core P _ k hP (good-bch-d B f g h2 h3 hB) h1) ) 
  ( λ g h0 h1 → let h3 = (from-passes-verify-n B g h0) in 
    prsv-n P B g h3 (correct-core P _ k hP (good-bch-n B g h3 hB) h1)) 
  ( λ g h0 h1 → let (h2 , h3) = from-passes-verify-p P B g h0 in 
    prsv-p P B g h2 (correct-core P _ k hP (good-bch-p P B g hP hB h2) h1) ) 
  ( λ g h0 h1 h2 → 
      let h3 = from-passes-num-verify-s B g h0 in 
      prsv-s P B g 
        (correct-core P _ k hP (good-bch-cons (not g) B h3 hB) h1) 
        (correct-core P _ k hP (good-bch-cons g B h3 hB) h2) ) 
  ( λ g h0 h1 → 
      let h2 = from-passes-num-verify-t B g h0 in
      prsv-t P B g h2 (correct-core P _ k hP (good-bch-t B g h2 hB) h1)) 
  λ h0 R F V hR → 
    ex-elim (from-ends-verify-x B h0) 
      λ g (h1 , h2) → 
        use-lem (R , F , V ⊢ g) 
          (λ h3 → not g , or-rgt h2 , dni h3) 
          λ h3 → g , or-rgt h1 , h3 

correct : ∀ P → good-prob P → ends (verify P [] 0) → unsat-prob P
correct P hP hp R F V hR =
  ex-elim (correct-core P [] 0 hP pall-nil hp R F V hR) 
    (λ f (h0 , h1) → f , or-elim h0 (λ h2 → h2 , h1) ⊥-elim)
    -}