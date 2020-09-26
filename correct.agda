module correct where

open import Data.Unit.Base 
open import Data.Unit.Polymorphic renaming (⊤ to ⊤*)
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Level
-- open import Agda.Builtin.String
open import Data.List renaming (or to disj) renaming(and to conj)
open import Data.Maybe.Base 
open import Data.Product
--   renaming (map to map?)
--   renaming (_>>=_ to _?>=_)
-- open import Agda.Builtin.Coinduction
-- import IO.Primitive as Prim
-- open import IO
--   renaming (_>>=_ to _>>>=_)
--   renaming (_>>_ to _>>>_)
open import basic 
--  renaming (_>>_ to _?>_)

data ⊥ : Set where

⊥* : {l : Level} → Set l
⊥* {l} = Lift l ⊥

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

largeType : Setω
largeType = {n : Level} → Set n

_∧_ = _×_

and-left : {l : Level} → {m : Level} → {A : Set l} → {B : Set m} → (A ∧ B) → A
and-left (h , _) = h

data _∨_ {l : Level} {m : Level} (A : Set l) (B : Set m) : Set (l ⊔ m) where
  or-left : A → A ∨ B
  or-right : B → A ∨ B

-- data _∨_ (A B : Set) : Set where
--   left : A → A ∨ B
--   right : B → A ∨ B

_↔_ : {l : Level} {m : Level} (A : Set l) (B : Set m) → Set (l ⊔ m) 
A ↔ B = (A → B) ∧ (B → A)

¬ : {l : Level} → (Set l) → Set l
¬ A = A → ⊥ 
  
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

is-true : Bool → Set 
is-true true = ⊤ 
is-true false = ⊥ 

_,_,_⊢_ : {A : Set} → Rls A → Fns A → Vas A → Form → Set
R , F , V ⊢ (cst b) = b ≡ true 
R , F , V ⊢ (not f) = ¬ (R , F , V ⊢ f)
R , F , V ⊢ (bct or f g) = (R , F , V ⊢ f) ∨ (R , F , V ⊢ g)
R , F , V ⊢ (bct and f g) = (R , F , V ⊢ f) ∧ (R , F , V ⊢ g)
R , F , V ⊢ (bct imp f g) = (R , F , V ⊢ f) → (R , F , V ⊢ g)
R , F , V ⊢ (bct iff f g) = (R , F , V ⊢ f) ↔ (R , F , V ⊢ g)
R , F , V ⊢ (qtf false f) = ∀ (x) → (R , F , (V ₀↦ x) ⊢ f)
R , F , V ⊢ (qtf true f) = ∃ (\ x → (R , F , (V ₀↦ x) ⊢ f))
R , F , V ⊢ (rel r ts) = (R r (terms-val F V ts)) ≡ true

_=*_ : Term → Term → Form
t =* s = rel (sf ('=' ∷ [])) (cons t (cons s nil))

standard : {A : Set} → Rls A → Fns A → Vas A → Set 
standard R F V = (t : Term) → (s : Term) → 
  ((R , F , V ⊢ (t =* s)) ↔ (term-val F V t ≡ term-val F V s))

unsat : Prob → Set₁
unsat P = ∀ (A : Set) (R : Rls A) F V → standard R F V → ∃ (\ n → ¬ (R , F , V ⊢ P n))

_∈_ : {A : Set} → A → List A → Set 
_∈_ _ [] = ⊥
_∈_ x (y ∷ ys) = (x ≡ y) ∨ (x ∈ ys)

or-elim : ∀ {l} {m} {k} {A : Set l} {B : Set m} {C : Set k} → A ∨ B → (A → C) → (B → C) → C
or-elim (or-left x) f g = f x
or-elim (or-right x) f g = g x

unsat-bch : Prob → Bch → Set₁
unsat-bch P fs = 
  ∀ (A : Set) (R : Rls A) F V → standard R F V → 
    ((∃ (\ n →  ¬ (R , F , V ⊢ P n))) ∨ (∃ (λ f → (f ∈ fs) ∧ ¬ (R , F , V ⊢ f))))

unsat-ext : Prob → List Bch → Set₁
unsat-ext P Bs = ∀ (B) → B ∈ Bs → unsat-bch P B 

unsat-state : State → Set₁
unsat-state (P ^ Bs ^ _ ^ _) = unsat-ext P Bs

exist-elim : ∀ {i} {j} {A : Set} {B : Set i} {P : A → Set j} → (∃ P) → (∀ (x : A) → P x → B) → B
exist-elim (a , h0) h1 = h1 a h0

-- not-member-nil : {l : Level} {A : Set l} → {x : A} → ¬ (x ∈ [])
-- not-member-nil {A} {x} ()

id : ∀ {l} {A : Set l} → A → A 
id x = x

false-elim : {l : Level} {A : Set l} → ⊥ → A
false-elim ()

not-elim : {l : Level} {m : Level} {A : Set l} {B : Set m} → A → (¬ A) → B
not-elim h0 h1 = false-elim (h1 h0)

pall : {A : Set} → (A → Set) → List A → Set
pall {A} p l = (x : A) → (x ∈ l) → p x

pall-nil : {A : Set} {p : A → Set} → pall p []
pall-nil {A} {p} x = false-elim

good-bch : Bch → Set
good-bch B = pall (\ f → true ≡ check-nf-form (length B) f) B

good-bchs : List Bch → Set
good-bchs Bs = pall good-bch Bs

eq-elim : ∀ {l} {A : Set l} {x : A} {y : A} (p : A → Set) → x ≡ y → p x → p y 
eq-elim p refl = id

eq-symm : ∀ {l} {A : Set l} {x : A} {y : A} → x ≡ y → y ≡ x
eq-symm refl = refl

ite-elim : ∀ {l} {A : Set} {x : A} {y : A} (b : Bool) → (P : A → Set l) → P x → P y → P (if b then x else y)
ite-elim true  _ hx _  = hx
ite-elim false _ _  hy = hy

state-good : State → Set
state-good S = good-bchs (State.Bchs S)

of-false :  ∀ {i} {j} {A : Set i} → ⊥* {j} → A
of-false ()

holds-or-nothing  : ∀ {l} {A : Set} → (P : A → Set l) → Maybe A → Set l
holds-or-nothing P nothing = ⊤* 
holds-or-nothing P (just x) = P x 

just-and-holds  : ∀ {l} {A : Set} → (P : A → Set l) → Maybe A → Set l
just-and-holds P m = ∃ (\ a → ((m ≡ (just a)) ∧ P a))

-- maybe-state-good : Maybe State → Set₁ 
-- maybe-state-good (just S) = state-good S
-- maybe-state-good nothing = ⊤


maybe-elim : ∀ {l} {A : Set} → (P : Maybe A → Set l) → (P nothing) → ((x : A) → P (just x)) → (m : Maybe A) → P m 
maybe-elim P hn hj nothing = hn
maybe-elim P hn hj (just x) = hj x

maybe-elim-conc : ∀ {i} {j} {A : Set} {m : Maybe A} → (P : Maybe A → Set i) → (Q : Set j) → 
  (P nothing → Q) → ((x : A) → P (just x) → Q) → P m → Q 
maybe-elim-conc P Q hn hj hm = maybe-elim (\ x → (P x → Q)) hn hj _ hm

transit-good : ∀ P Bs As Is → good-bchs Bs → holds-or-nothing state-good (transit P Bs As Is) 
transit-good = {!   !}

transit-unsat : ∀ P Bs As Is → just-and-holds unsat-state (transit P Bs As Is) → unsat-ext P Bs 
transit-unsat = {!   !}

maybe-absurd : ∀ {i} {j} {A : Set i} {B : Set j} {x : A} → nothing ≡ (just x) → B 
maybe-absurd ()

of-bind-eq-just : ∀ {i} {j} {A : Set i} {B : Set j} → 
  (f : Maybe A) → (g : A → Maybe B) → (b : B) → 
  (f >>= g) ≡ just b → ∃ (\ a → (f ≡ just a) ∧ (g a ≡ just b))
of-bind-eq-just nothing g b = maybe-absurd
of-bind-eq-just (just a) g b = \ h → (a , (refl , h))

foo : State → State 
foo (P ^ Bs ^ As ^ (_ ∷ Is)) = foo (P ^ Bs ^ As ^ Is)
foo s = s

data State' : Set where
  _$_ : List Inst →  List Arg → State'

transit' : State' → Maybe State'
transit' ((app-a ∷ []) $ (bool b' ∷ nat n' ∷ [])) = nothing
transit' ((mk-nat ∷ IS) $ (chars cs ∷ AS))= do
  k' ← chars-to-nat cs 
  transit' (IS $ (nat k' ∷ AS))
-- do
--   f ← get-from-bch B n' >>= break-a b'  
--   -- just (P $ (f ∷ B) ∷ Bs $ [] $ []) 
--   nothing 
-- transit' P (B ∷ Bs) (nat n' ∷ []) (app-b ∷ []) = do
--   (f , g) ← get-from-bch B n' >>= break-b 
--   just (P ^ (f ∷ B) ∷ (g ∷  B) ∷ Bs ^ [] ^ [])
-- transit' P (B ∷ Bs) (term t' ∷ nat n' ∷ []) (app-c ∷ []) = do
--   just-if (check-gnd-term 0 t')
--   just-if (check-nf-term ((length B) + 1) t')
--   f ← get-from-bch B n' >>= break-c t' 
--   just (P ^ (f ∷ B) ∷ Bs ^ [] ^ []) 
-- transit' P (B ∷ Bs) (nat n' ∷ []) (app-d ∷ []) = do
--   f ← get-from-bch B n' >>= break-d (length B) 
--   just (P ^ (f ∷ B) ∷ Bs ^ [] ^ []) 
-- transit' P (B ∷ Bs) (nat n' ∷ []) (app-n ∷ []) = do
--   f ← get-from-bch B n' >>= break-n 
--   just (P ^ (f ∷ B) ∷ Bs ^ [] ^ []) 
-- transit' P (B ∷ Bs) (chars cs ∷ []) (app-p ∷ []) = do
--   just-if (check-gnd-form 0 (P cs))
--   just-if (check-nf-form ((length B) + 1) (P cs))
--   just (P ^ ((P cs) ∷ B) ∷ Bs ^ [] ^ []) 
-- transit' P (B ∷ Bs) (form f ∷ []) (app-s ∷ []) = do
--   just-if (check-gnd-form 0 f)
--   just-if (check-nf-form ((length B) + 1) f)
--   just (P ^ ((not f) ∷ B) ∷ (f ∷ B) ∷ Bs ^ [] ^ []) 
-- transit' P (B ∷ Bs) (form f ∷ []) (app-t ∷ []) = do
--   just-if (check-gnd-form 0 f)
--   just-if (check-nf-form ((length B) + 1) f)
--   just-if (justified (length B) f) 
--   just (P ^ (f ∷ B) ∷ Bs ^ [] ^ []) 
-- transit' P (B ∷ Bs) (nat n' ∷ nat p' ∷ []) (app-x ∷ []) = do
--   f ← get-from-bch B p'
--   g ← get-from-bch B n' 
--   if eq-form (not f) g then ( just (P ^ Bs ^ [] ^ []) ) else nothing
-- transit' P Bs (As) (get-nat ∷ IS) = 
--   just (P ^ Bs ^ (chars [] ∷ As) ^ (acc-chars ∷ mk-nat ∷ IS)) 
-- transit' P Bs (As) (get-chars ∷ IS) = 
--   just (P ^ Bs ^ (chars [] ∷ As) ^ (acc-chars ∷ IS)) 
-- transit' (P ^ Bs ^ nat n' ∷ AS ^ (mk-var ∷ IS)) = transit' (P ^ Bs ^ term (var n') ∷ AS ^ IS) 
-- transit' P Bs (terms ts ∷ ftr f ∷ AS) (mk-fun ∷ IS)= transit' P Bs (term (fun f ts) ∷ AS) IS 
-- transit' P Bs (terms ts ∷ ftr f ∷ AS) (mk-rel ∷ IS)= transit' P Bs (form (rel f ts) ∷ AS) IS 
-- transit' P Bs (bool b' ∷ AS) (mk-cst ∷ IS)= transit' P Bs (form (cst b') ∷ AS) IS 
-- transit' P Bs (form f ∷ AS) (mk-not ∷ IS)= transit' P Bs (form (not f) ∷ AS) IS 
-- transit' P Bs (form g' ∷ form f' ∷ bct b' ∷ AS) (mk-bct ∷ IS)= transit' P Bs (form (bct b' f' g') ∷ AS) IS 
-- transit' P Bs (form f' ∷ bool b' ∷ AS) (mk-qtf ∷ IS)= transit' P Bs (form (qtf b' f') ∷ AS) IS 
-- transit' (P ^ Bs ^ terms ts' ∷ term t' ∷ AS ^ (mk-cons ∷ IS)) = transit' (P ^ Bs ^ terms (cons t' ts') ∷ AS ^ IS)
-- transit' (P ^ Bs ^ nat n' ∷ AS ^ (mk-nf ∷ IS)) =   transit' (P ^ Bs ^ ftr (nf n') ∷ AS ^ IS)
-- transit' (P ^ Bs ^ chars cs ∷ AS ^ (mk-sf ∷ IS)) = transit' (P ^ Bs ^ ftr (sf cs) ∷ AS ^ IS)
transit' s = nothing -- just s

correct-core : ∀ cs P Bs As Is → (check cs (P ^ Bs ^ As ^ Is) ≡ just tt) → good-bchs Bs → unsat-ext P Bs
correct-core _ _ [] _ _ hc hg = \ _ → \ hB → false-elim hB
correct-core (c ∷ cs) P (B ∷ Bs) As [] hc hg = {!   !}
 -- ite-elim (c =c 'A') (λ x → x ≡ just tt → unsat-ext P (B ∷ Bs)) 
 --   (\ hi → correct-core cs P (B ∷ Bs) (chars [] ∷ []) ((acc-chars ∷ mk-nat ∷ get-bool ∷ app-a ∷ [])) hi hg) 
 --   {!   !} 
 --   hc


correct-core (c ∷ cs) P (B ∷ Bs) As (get-bool ∷ Is) hc hg = 
  ite-elim (c =c 'T') (λ x → x ≡ just tt → unsat-ext P (B ∷ Bs)) 
    (
      \ h0 → exist-elim 
        (of-bind-eq-just (transit P (B ∷ Bs) (bool true ∷ As) Is) (check cs) tt h0) 
        \ s → \ h1 → transit-unsat _ _ (bool true ∷ As) Is 
          ((s , (and-left h1 , {!   !})))
    ) -- (\ hi → maybe-elim-conc (\ x → x ≡ just tt) _ maybe-absurd {!   !} hi) 
    {!   !} 
    hc  
correct-core (c ∷ cs) P Bs As (get-term ∷ Is)  hc hg = {!   !}
correct-core (c ∷ cs) P Bs As (get-terms ∷ Is) hc hg = {!   !} 
correct-core (c ∷ cs) P Bs As (get-ftr ∷ Is)   hc hg = {!   !} 
correct-core (c ∷ cs) P Bs As (get-form ∷ Is)  hc hg = {!   !}
correct-core (c ∷ cs) P Bs (chars cs1 ∷ AS) (acc-chars ∷ Is) hc hg = {!   !}

correct : (cs : Chars) (P : Prob) → (check cs (P ^ ([] ∷ []) ^ [] ^ []) ≡ just tt) → unsat P
correct cs P h0 A R F V hs = 
  let h2 : unsat-bch P []
      h2 = correct-core cs P ([] ∷ []) [] [] h0 (\ x → \ hx → or-elim hx (\ hx2 → eq-elim good-bch (eq-symm hx2) pall-nil) false-elim) [] (or-left refl) in
  let h3 = h2 A R F V hs in
  or-elim h3 (\ x → x) \ h4 → exist-elim h4 \ f → \ h5 → not-elim (and-left h5) id
  
