module correct (D : Set) where

open import Data.Empty
open import Relation.Nullary
open import Data.Unit.Base 
open import Data.Unit.Polymorphic renaming (⊤ to ⊤*)
open import Data.Bool
  renaming (_<_ to _<b_)
  renaming (_∧_ to _&&_)
  renaming (_∨_ to _||_)
open import Agda.Builtin.Nat
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Data.List renaming (or to disj) renaming(and to conj)
open import Data.Maybe
  renaming (_>>=_ to _?>=_)
  renaming (is-just to is-just-bool)
--   renaming (map to map?)
open import Data.Product
-- open import Agda.Builtin.Coinduction
-- import IO.Primitive as Prim
-- open import IO
--   renaming (_>>=_ to _>>>=_)
--   renaming (_>>_ to _>>>_)
open import basic 
open import verify 
--  renaming (_>>_ to _?>_)
 
postulate LEM : (A : Set) → Dec A
-- 
-- ⊥* : {l : Level} → Set l
-- ⊥*  = Lift l ⊥

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

-- data _∨_ (A B : Set) : Set where
--   left : A → A ∨ B
--   right : B → A ∨ B

_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)
  
-- Σ-syntax = Σ
-- infix 2 Σ-syntax
-- syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
-- 
-- ∃ : ∀ {A : Set} (B : A → Set) → Set
-- ∃ {A} B = Σ A B

-- ∃-syntax = ∃
-- syntax ∃-syntax (λ x → B) = ∃[ x ] B
-- 
-- ∀-syntax : ∀ {A : Set} (P : A → Set) → Set
-- ∀-syntax {A} P = ∀ {x : A} → P x
-- syntax ∀-syntax (λ x → B) = ∀[ x ] B

termoid-val : Fns → Vas → {b : Bool} → Termoid b → ElemList D b
termoid-val _ V (var k) = V k
termoid-val F V (fun f ts) = F f (termoid-val F V ts)
termoid-val F V nil = []
termoid-val F V (cons t ts) = (termoid-val F V t) ∷ (termoid-val F V ts)

term-val : Fns → Vas → Term → D
term-val F V t = termoid-val F V t

terms-val : Fns → Vas → Terms → List D
terms-val F V ts = termoid-val F V ts

_₀↦_ : Vas → D → Vas 
_₀↦_ V a 0 = a
_₀↦_ V a (suc k) = V k

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
R , F , V ⊢ (qtf false f) = ∀ (x) → (R , F , (V ₀↦ x) ⊢ f)
R , F , V ⊢ (qtf true f) = ∃ (\ x → (R , F , (V ₀↦ x) ⊢ f))
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
good-form k f = ∀ m → nf-in-form m f → ((m < k) ≡ true)

good-bch : Bch → Set
good-bch B = pall (good-form (length B)) B

eq-elim : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → x ≡ y → p x → p y 
eq-elim p refl = id

eq-symm : ∀ {A : Set} {x : A} {y : A} → x ≡ y → y ≡ x
eq-symm refl = refl

ite-elim : ∀ {A : Set} {x : A} {y : A} (b : Bool) → 
  (P : A → Set) → P x → P y → P (if b then x else y)
ite-elim false P hx hy = hy
ite-elim true  P hx hy = hx

mp : {A B : Set} → A → (A → B) → B
mp h0 h1 = h1 h0 

modus-tollens : ∀ {A : Set} {B : Set} → (A → B) → ¬ B → ¬ A  
modus-tollens h0 h1 h2 = ⊥-elim (h1 (h0 h2))

holds-or-nothing  : ∀ {A : Set} → (P : A → Set) → Maybe A → Set
holds-or-nothing P nothing = ⊤* 
holds-or-nothing P (just x) = P x 

just-and-holds  : ∀ {A : Set} → (P : A → Set) → Maybe A → Set
just-and-holds P m = ∃ (\ a → ((m ≡ (just a)) ∧ P a))


-- maybe-state-good : Maybe State → Set₁ 
-- maybe-state-good (just S) = state-good S
-- maybe-state-good nothing = ⊤

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

just-inj : ∀  {A : Set} {a b : A} → (just a ≡ just b) → a ≡ b
just-inj refl = refl

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

good-bch-cons : ∀ f B → good-form (suc (length B)) f → good-bch B → good-bch (f ∷ B)
good-bch-cons f B h0 h1 g h2 = or-elim h2 
  (\ h3 → eq-elim _ (eq-symm h3) h0) 
  \ h3 k h4 → {!   !}

prsv-a : ∀ P B b f g → f ∈ B → (break-a b f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-a P B b f g h0 h1 = prsv-implies P B f g h0 (implies-a _ _ _ h1) 

prsv-good-a : ∀ B b f g → f ∈ B → (break-a b f ≡ just g) → good-bch B → good-bch (f ∷ B)
prsv-good-a B b f g h0 h1 = {!   !}

-- unsat-cons-to-unsat : ∀ P B f → unsat P (f ∷ B) → unsat P B 
-- unsat-cons-to-unsat P B f h0 R F V h1 = 
--   exist-elim (h0 R F V h1) \ g h2 → (g , {!   !})
 
cong :
  {A : Set}
  {B : Set}
  (f : A → B)
  {x y : A}
  (p : x ≡ y)
  → -----------
  f x ≡ f y
cong _ refl = refl

is-just : ∀  {A : Set} → Maybe A → Set
is-just nothing = ⊥
is-just (just _) = ⊤

from-is-just : ∀ {A} {B} → (f : Read A) → (g : A → Read B) → 
  ∀ cs → is-just ((f >>= g) cs) → 
    ∃ (\ x → ∃ (\ cs' → (f cs ≡ just (x , cs')) ∧ (is-just (g x cs'))))
from-is-just f g cs with f cs 
... | nothing = \ h0 → ⊥-elim h0 
... | (just (x , cs')) = \ h0 → (x , (cs' , (refl , h0)))

prod-inj-left : ∀ {A B : Set} {a0 a1 : A} {b0 b1 : B} → 
  (a0 , b0) ≡ (a1 , b1) → a0 ≡ a1
prod-inj-left refl = refl

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

-- from-in-reverse : ∀ {A : Set} (x : A) l → x ∈ (reverse l) → x ∈ l 
-- from-in-reverse x [] = id
-- from-in-reverse x (y ∷ ys) h0 = {!   !}

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

correct-core : ∀ P B N cs → is-just (verify P B N cs) → good-bch B → unsat P B
correct-core P B (suc k) (c ∷ cs) = 
  ite-elim (c ==c 'A') (\ (x : Read ⊤) → is-just (x cs) → good-bch B → unsat P B) 
    ( use-is-just-bind read-nat _ cs \ m cs0 h0 →  
      use-is-just-bind read-bool _ cs0 \ b cs1 h1 → 
        use-is-just-bind 
          (lift-read (get-bch B m ?>= break-a b)) 
          (\ f → verify P (f ∷ B) k) cs1 \ f cs2 h2 h3 h4 → 
            exist-elim (from-lift-read-get-bch B m (break-a b) f _ _ h2) 
            \ g h5 → prsv-a P B b _ _ (and-left h5) 
              (and-right h5) 
              (correct-core P (f ∷ B) k _ h3 {!   !}) )
           {!  !} 
  -- ite-elim (\ x → is-just (x cs) → good-bch B → unsat P B) 
  --   {!   !} 
  --   {!   !}

correct : ∀ P N cs → is-just (verify P [] N cs) → unsat-prob P
correct P N cs h0 R F V h1 = 
  exist-elim (correct-core P [] N cs h0 pall-nil R F V h1) 
    \ f → \ h2 → (f , or-elim (and-left h2) (\ h3 → (h3 , and-right h2)) ⊥-elim)  
    
  
