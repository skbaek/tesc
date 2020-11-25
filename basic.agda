module basic where

open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
  renaming (_==_ to _=n_)
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
  renaming (_>>=_ to _o>=_)
  renaming (map to map?)
open import Data.Nat.Show
open import Data.Empty
open import Relation.Nullary.Decidable using (toWitness)

postulate LEM : (A : Set) → Dec A
postulate FX : ∀ {A B : Set} (f g : A → B) (h : ∀ a → f a ≡ f a) → f ≡ g

id : ∀ {l} {A : Set l} → A → A 
id x = x



-- Bool & Logic --

fst : {A : Set} {B : Set} → (A × B) → A 
fst (x , _) = x 

snd : {A : Set} {B : Set} → (A × B) → B
snd (_ , y) = y

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

ex-elim : ∀ {l0 l1 l2} {A : Set l0} {B : Set l1} {P : A → Set l2} → (∃ P) → (∀ (x : A) → P x → B) → B
ex-elim (a , h0) h1 = h1 a h0

ex-el-2 : ∀ {A B C : Set} {P : A → B → Set} → 
  (∃ λ a → ∃ (P a)) → (∀ (x : A) (y : B) → P x y → C) → C
ex-el-2 (a , (b , h0)) h1 = h1 a b h0

ex-el-3 : ∀ {A B C D : Set} {P : A → B → C → Set} → 
  (∃ λ a → ∃ λ b → ∃ λ c → (P a b c)) → (∀ a b c → P a b c → D) → D
ex-el-3 (a , (b , (c , h0))) h1 = h1 a b c h0

ex-elim' : ∀ {A B : Set} {P : A → Set} → (∀ (x : A) → P x → B) → (∃ P) → B
ex-elim' h0 (a , h1) = h0 a h1

ex-el-3' : ∀ {A B C D : Set} {P : A → B → C → Set} → 
  (∀ a b c → P a b c → D) → (∃ λ a → ∃ λ b → ∃ λ c → (P a b c)) → D
ex-el-3' h0 (a , (b , (c , h1))) = h0 a b c h1

el-lem : ∀ (A : Set) {B : Set} → (A → B) → ((¬ A) → B) → B
el-lem A h0 h1 with LEM A 
... | (yes h2) = h0 h2
... | (no h2)  = h1 h2

dni : ∀ {A : Set} → A → (¬ (¬ A))
dni h0 h1 = h1 h0

dne : ∀ {A : Set} → (¬ ¬ A) → A 
dne {A} h0 = el-lem A id λ h1 → ⊥-elim (h0 h1)

fs : Bool → Set
fs true  = ⊥
fs false = ⊤

not-or-lft : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ A 
not-or-lft h0 h1 = h0 (or-lft h1)  

not-or-rgt : ∀ {A B : Set} → ¬ (A ∨ B) → ¬ B 
not-or-rgt h0 h1 = h0 (or-rgt h1)  

not-imp-lft : ∀ {A B : Set} → ¬ (A → B) → A 
not-imp-lft {A} {B} h0 = el-lem  A id λ h1 → ⊥-elim (h0 λ h2 → ⊥-elim (h1 h2))

not-imp-rgt : ∀ {A B : Set} → ¬ (A → B) → ¬ B 
not-imp-rgt {A} {B} h0 h1 = ⊥-elim (h0 λ h2 → h1)

imp-to-not-or :  ∀ {A B} → (A → B) → ((¬ A) ∨ B)
imp-to-not-or {A} {B} h0 = el-lem A (λ h1 → or-rgt (h0 h1)) or-lft 

not-and-to-not-or-not :  ∀ {A B} → ¬ (A ∧ B) → ((¬ A) ∨ (¬ B))
not-and-to-not-or-not {A} {B} h0 = el-lem A 
  (λ h1 → el-lem B (λ h2 → ⊥-elim (h0 (h1 , h2))) or-rgt) 
  or-lft

el-tr-fs : ∀ {b : Bool} {A : Set} → tr b → fs b → A 
el-tr-fs {true} _ ()
el-tr-fs {false} ()

_⇔_ : Bool → Bool → Bool 
true ⇔ true = true
false ⇔ false = true
_ ⇔ _  = false

rt : Set → Bool
rt A = el-lem A (λ _ → true) (λ _ → false)

tr-rt-iff : ∀ {A : Set} → tr (rt A) ↔ A 
tr-rt-iff {A} with LEM A 
... | (yes h0) = (λ _ → h0) , (λ _ → tt)
... | (no h0) = ⊥-elim , h0

el-bor : ∀ {A : Set} b1 b2 → (tr b1 → A) → (tr b2 → A) → tr (b1 || b2) → A
el-bor true _ h0 _ h2 = h0 tt
el-bor _ true _ h1 h2 = h1 tt

biff-to-eq : ∀ {b0 b1} → tr (b0 ⇔ b1) → (b0 ≡ b1)
biff-to-eq {true} {true} _ = refl
biff-to-eq {false} {false} _ = refl

iff-refl : ∀ {A : Set} → (A ↔ A)
iff-refl = (id , id)

not-iff-not-to-iff : ∀ {A B} → ((¬ A) ↔ (¬ B)) → (A ↔ B)
not-iff-not-to-iff h0 = 
  (λ h1 → dne (λ h2 → snd h0 h2 h1)) ,
  (λ h1 → dne (λ h2 → fst h0 h2 h1)) 

mp : {A B : Set} → A → (A → B) → B
mp h0 h1 = h1 h0 

modus-tollens : ∀ {A : Set} {B : Set} → (A → B) → ¬ B → ¬ A  
modus-tollens h0 h1 h2 = ⊥-elim (h1 (h0 h2))

iff-to-not-iff-not : ∀ {A B} → (A ↔ B) → ((¬ A) ↔ (¬ B))
iff-to-not-iff-not h0 = 
  ( (λ ha hb → ⊥-elim (ha (snd h0 hb))) , 
    (λ hb ha → ⊥-elim (hb (fst h0 ha))) ) 

or-iff-or : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∨ B0) ↔ (A1 ∨ B1))
or-iff-or ha hb = 
  (λ h0 → or-elim h0 
    (λ h1 → (or-lft (fst ha h1))) 
    (λ h1 → (or-rgt (fst hb h1)))) , 
  (λ h0 → or-elim h0 
    (λ h1 → (or-lft (snd ha h1))) 
    (λ h1 → (or-rgt (snd hb h1)))) 

iff-symm : ∀ {A B} → (A ↔ B) → (B ↔ A) 
iff-symm h0 = (λ h1 → snd h0 h1) , (λ h1 → fst h0 h1)

iff-trans : ∀ {A} B {C} → (A ↔ B) → (B ↔ C) → (A ↔ C)
iff-trans _ h0 h1 = 
  (λ h2 → fst h1 (fst h0 h2)) , 
  (λ h2 → snd h0 (snd h1 h2))

and-iff-and : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ∧ B0) ↔ (A1 ∧ B1))
and-iff-and ha hb = 
  (λ h0 → (fst ha (fst h0) , fst hb (snd h0))) , 
  (λ h0 → (snd ha (fst h0) , snd hb (snd h0)))

imp-iff-imp : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 → B0) ↔ (A1 → B1))
imp-iff-imp ha hb = 
  (λ h0 h1 → fst hb (h0 (snd ha h1))) , 
  (λ h0 h1 → snd hb (h0 (fst ha h1)))

iff-iff-iff : ∀ {A0 A1 B0 B1} → (A0 ↔ A1) → (B0 ↔ B1) → ((A0 ↔ B0) ↔ (A1 ↔ B1))
iff-iff-iff ha hb =  
  (λ h0 → iff-trans _ (iff-symm ha) (iff-trans _  h0 hb)) ,
  (λ h0 → iff-trans _ ha (iff-trans _ h0 (iff-symm hb)))

fa-iff-fa : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∀ a → P a) ↔ (∀ a → Q a))
fa-iff-fa h0 = ((λ h1 a → fst (h0 a) (h1 a)) , (\h1 a → snd (h0 a) (h1 a)))

ex-iff-ex : ∀ {A} {P Q : A → Set} → (∀ a → (P a ↔ Q a)) → ((∃ P) ↔ (∃ Q))
ex-iff-ex h0 = 
  (λ h1 → ex-elim h1 (λ a h2 → a , fst (h0 a) h2)) , 
  (λ h2 → ex-elim h2 (λ a h2 → a , snd (h0 a) h2))

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

band-to-fst : ∀ a b → tr (a && b) → tr a 
band-to-fst true _ _ = tt

band-to-snd : ∀ a b → tr (a && b) → tr b 
band-to-snd _ true _ = tt
band-to-snd true false ()

band-to-and : ∀ a b → tr (a && b) → (tr a ∧ tr b)
band-to-and true true _ = tt , tt

band-to-and-3 : ∀ a b c → tr (a && b && c) → (tr a ∧ tr b ∧ tr c)
band-to-and-3 true true true _ = tt , tt , tt

band-to-and-4 : ∀ a b c d → tr (a && b && c && d) → (tr a ∧ tr b ∧ tr c ∧ tr d)
band-to-and-4 true true true true _ = tt , tt , tt , tt

band-to-and-5 : ∀ a b c d e → tr (a && b && c && d && e) → (tr a ∧ tr b ∧ tr c ∧ tr d ∧ tr e)
band-to-and-5 true true true true true _ = tt , tt , tt , tt , tt

ex-falso : ∀ {A B : Set} → A → ¬ A → B
ex-falso h0 h1 = ⊥-elim (h1 h0)

top-iff : ∀ {P} → P → (⊤ ↔ P)
top-iff h0 = (λ _ → h0) , (λ _ → tt)

el-ite : ∀ {A B : Set} (P : A → Set) (b : Bool) (a0 a1 : A) → 
  (P a0 → B) → (P a1 → B) → P (if b then a0 else a1) → B
el-ite _ true _ _ h0 _ h1 = h0 h1
el-ite _ false _ _ _ h0 h1 = h0 h1

el-ite' : ∀ {A B : Set} (P : A → Set) (b : Bool) (a0 a1 : A) → 
  P (if b then a0 else a1) → (P a0 → B) → (P a1 → B) → B
el-ite' P b a0 a1 h h0 h1 = el-ite P b a0 a1 h0 h1 h

intro-ite : ∀ {A : Set} {x : A} {y : A} (b : Bool) → 
  (P : A → Set) → P x → P y → P (if b then x else y)
intro-ite false P hx hy = hy
intro-ite true  P hx hy = hx

intro-ite-lem : ∀ {A : Set} {x y : A} (b : Bool) → 
  (P : A → Set) → (tr b → P x) → (fs b → P y) → P (if b then x else y)
intro-ite-lem false P hx hy = hy tt
intro-ite-lem true  P hx hy = hx tt

    



-- Equality --

cong : ∀ {A B : Set} (f : A → B) {x y : A} (p : x ≡ y) →  f x ≡ f y
cong _ refl = refl

cong-2 : ∀ {A B C : Set} (f : A → B → C) {x y : A} {z w : B} → x ≡ y → z ≡ w → f x z ≡ f y w
cong-2 _ refl refl = refl

cong-3 : ∀ {A B C D : Set} (f : A → B → C → D) {a0 a1 : A} {b0 b1 : B} {c0 c1 : C} → 
  a0 ≡ a1 → b0 ≡ b1 → c0 ≡ c1 → f a0 b0 c0 ≡ f a1 b1 c1
cong-3  f refl refl refl = refl 

cong-fun-arg : ∀ {A B : Set} {x0 x1 : A → B} {y0 y1 : A} → 
  x0 ≡ x1 → y0 ≡ y1 → (x0 y0 ≡ x1 y1)
cong-fun-arg refl refl = refl

_≠_ : {A : Set} → A → A → Set 
x ≠ y = ¬ (x ≡ y)

el-eq-symm : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p y → p x 
el-eq-symm p refl = id

el-eq : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p x → p y 
el-eq p refl = id

el-eq-2 : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} (p : A → B → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → p a0 b0 → p a1 b1 
el-eq-2 p refl refl = id

el-eq-3 : ∀ {A B C : Set} {a0 a1 : A} {b0 b1 : B} {c0 c1 : C} (p : A → B → C → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → c0 ≡ c1 → p a0 b0 c0 → p a1 b1 c1
el-eq-3 p refl refl refl = id

el-eq-4 : ∀ {A B C D : Set} {a0 a1 : A} {b0 b1 : B} 
  {c0 c1 : C} {d0 d1 : D} (p : A → B → C → D → Set) → 
  a0 ≡ a1 → b0 ≡ b1 → c0 ≡ c1 → d0 ≡ d1 → p a0 b0 c0 d0 → p a1 b1 c1 d1
el-eq-4 p refl refl refl refl = id

eq-trans : ∀ {A : Set} {x : A} (y : A) {z : A} → x ≡ y → y ≡ z → x ≡ z
eq-trans _ refl refl = refl

eq-symm : ∀ {A : Set} {x : A} {y : A} → x ≡ y → y ≡ x
eq-symm refl = refl

eq-to-iff : ∀ {A : Set} (P : A → Set) (x y : A) → x ≡ y → ((P x) ↔ (P y))
eq-to-iff P x y refl = iff-refl  

eq-to-iff-2 : ∀ {A B : Set} (P : A → B → Set) (a0 a1 : A) (b0 b1 : B) → 
  a0 ≡ a1 → b0 ≡ b1 → ((P a0 b0) ↔ (P a1 b1))
eq-to-iff-2 P a0 a1 b0 b1 refl refl = iff-refl  



-- Nat --

pred : Nat → Nat
pred 0 = 0
pred (suc k) = k

suc-inj : ∀ {a b : Nat} → (suc a ≡ suc b) → a ≡ b
suc-inj refl = refl

data _<_ : Nat → Nat → Set where
  0< : ∀ k → 0 < (suc k)
  suc< : ∀ k m → k < m → suc k < suc m

_>_ : Nat → Nat → Set 
k > m = m < k

lt-or-eq-or-gt : ∀ k m → ((k < m) ∨ ((k ≡ m) ∨ (k > m)))
lt-or-eq-or-gt 0 0 = or-rgt (or-lft refl)
lt-or-eq-or-gt 0 (suc m) = or-lft (0< _)
lt-or-eq-or-gt (suc k) 0 = or-rgt (or-rgt (0< _))
lt-or-eq-or-gt (suc k) (suc m) = 
  or-elim (lt-or-eq-or-gt k m) 
    (λ h0 → or-lft (suc< _ _ h0)) 
    λ h0 → or-elim h0 
      (λ h1 → or-rgt (or-lft (cong suc h1))) 
      λ h1 → or-rgt (or-rgt (suc< _ _ h1))

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
  
lt-to-lt-suc : ∀ {k m} → (k < m) → (k < (suc m))
lt-to-lt-suc {0} _ = 0< _
-- lt-to-lt-suc {suc k} {0} ()
lt-to-lt-suc {suc k} {suc m} (suc< k m h) = suc< k _ (lt-to-lt-suc h)

not-<-self : ∀ k → ¬ (k < k)
not-<-self 0 ()
not-<-self (suc k) (suc< m m h) = not-<-self k h

lt-to-not-eq : ∀ k m → k < m → ¬ (k ≡ m)
lt-to-not-eq k m h0 h1 = not-<-self m (el-eq (λ x → x < m) h1 h0)

lt-to-not-gt : ∀ k m → k < m → ¬ (k > m)
lt-to-not-gt 0 0 ()
lt-to-not-gt 0 (suc k) _ ()
lt-to-not-gt (suc k) 0 ()
lt-to-not-gt (suc k) (suc m) (suc< _ _ h0) (suc< _ _ h1) = 
  lt-to-not-gt _ _ h0 h1

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





-- List --

_∈_ : {A : Set} → A → List A → Set
a0 ∈ [] = ⊥ 
a0 ∈ (a1 ∷ as) = (a0 ≡ a1) ∨ (a0 ∈ as)

eq-list : {A : Set} → (A → A → Bool) → List A → List A → Bool
eq-list f [] [] = true
eq-list f (x1 ∷ xs1) (x2 ∷ xs2) = f x1 x2 && (eq-list f xs1 xs2)
eq-list f _ _ = false

pall : {A : Set} → (A → Set) → List A → Set
pall {A} p l = ∀ (x : A) →  (x ∈ l) → p x

pall-nil : {A : Set} {p : A → Set} → pall p []
pall-nil {A} {p} x = ⊥-elim

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

intro-el-lem : ∀ {A B : Set} (C : B → Set) {f : A → B} {g : (¬ A) → B} → 
  (∀ (x : A) → C (f x)) → (∀ (x : ¬ A) → C (g x)) → C (el-lem A f g) 
intro-el-lem {A} {B} C {f} {g} hf hg with LEM A  
... | (yes h0) = hf h0 
... | (no h0) = hg h0 

intro-el-lem-yes : ∀ {A B : Set} (C : B → Set) {f : A → B} {g : (¬ A) → B} → 
  (∀ (x : A) → C (f x)) → A → C (el-lem A f g) 
intro-el-lem-yes {A} {B} C {f} {g} hf hA = intro-el-lem C hf λ h0 → ⊥-elim (h0 hA)

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



-- Misc --

Chars : Set
Chars = List Char 

chars-eq : Chars → Chars → Bool
chars-eq [] [] = true
chars-eq (c0 ∷ cs0) (c1 ∷ cs1) = (c0 =c c1) && (chars-eq cs0 cs1)
chars-eq _ _ = false

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
chars-to-nat-acc k (c ∷ cs) = char-to-nat c o>= λ m → chars-to-nat-acc ((k * 10) + m) cs

chars-to-nat : List Char → Maybe Nat  
chars-to-nat = chars-to-nat-acc 0

just-if : Bool → Maybe ⊤ 
just-if true = just tt
just-if false = nothing

just-inj : ∀  {A : Set} {a b : A} → (just a ≡ just b) → a ≡ b
just-inj refl = refl

prod-inj-lft : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} → 
  (a0 , b0) ≡ (a1 , b1) → a0 ≡ a1
prod-inj-lft refl = refl

prod-inj-rgt : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} → 
  (a0 , b0) ≡ (a1 , b1) → b0 ≡ b1
prod-inj-rgt refl = refl

holds-or-nothing  : ∀ {A : Set} → (P : A → Set) → Maybe A → Set
holds-or-nothing P nothing = ⊤ 
holds-or-nothing P (just x) = P x 

just-and-holds  : ∀ {A : Set} → (P : A → Set) → Maybe A → Set
just-and-holds P m = ∃ (λ a → ((m ≡ (just a)) ∧ P a))

maybe-elim : ∀ {A : Set} → (P : Maybe A → Set) → 
  (P nothing) → ((x : A) → P (just x)) → (m : Maybe A) → P m 
maybe-elim P hn hj nothing = hn
maybe-elim P hn hj (just x) = hj x

maybe-el-conc : ∀ {A : Set} {m : Maybe A} → (P : Maybe A → Set) → (Q : Set) → 
  (P nothing → Q) → ((x : A) → P (just x) → Q) → P m → Q 
maybe-el-conc P Q hn hj hm = maybe-elim (λ x → (P x → Q)) hn hj _ hm

maybe-absurd : ∀ {A B : Set} {x : A} → nothing ≡ (just x) → B 
maybe-absurd ()

char-eq-to-eq : ∀ c0 c1 → tr (c0 =c c1) → c0 ≡ c1 
char-eq-to-eq c0 c1 = toWitness

chars-eq-to-eq : ∀ cs0 cs1 → tr (chars-eq cs0 cs1) → cs0 ≡ cs1 
chars-eq-to-eq [] [] _ = refl
chars-eq-to-eq (c0 ∷ cs0) (c1 ∷ cs1) h0 = 
  cong-2 _∷_ 
    (toWitness (band-to-fst (c0 =c c1) _ h0)) 
    (chars-eq-to-eq cs0 cs1 (band-to-snd _ _ h0))