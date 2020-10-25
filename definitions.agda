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

postulate LEM : (A : Set) → Dec A
postulate FX : ∀ {A B : Set} (f g : A → B) (h : ∀ a → f a ≡ f a) → f ≡ g

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
 