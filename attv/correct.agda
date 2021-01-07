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
open import Data.Char
  renaming (_==_ to _=c_)
  renaming (_<_ to _<c_)
open import Agda.Builtin.Equality
open import Data.List renaming (or to disj) renaming(and to conj)
open import Data.Maybe
  renaming (_>>=_ to _o>=_)
open import Data.Product
open import basic 
open import verify 

Rel : Set  
Rel = List D → Bool

Fun : Set 
Fun = List D → D

const-fun : D → Fun 
const-fun d _ = d

RA : Set 
RA = Ftr → Rel 

FA : Set
FA = Ftr → Fun

VA : Set 
VA = Nat → D

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

_/_↦r_ : RA → Ftr → Rel → RA 
(R / f0 ↦r r) f1 = if (ftr-eq f0 f1) then r else R f1

_/_↦f_ : FA → Ftr → Fun → FA 
(F / f0 ↦f f) f1 = if (ftr-eq f0 f1) then f else F f1

_/_↦_ : VA → Nat → D → VA 
(V / k ↦ d) m = tri k (V (pred m)) d (V m) m

_,_,_⊨_ : RA → FA → VA → Form → Set
R , F , V ⊨ (cst b) = tr b 
R , F , V ⊨ (not f) = ¬ (R , F , V ⊨ f)
R , F , V ⊨ (bct or f g) = (R , F , V ⊨ f) ∨ (R , F , V ⊨ g)
R , F , V ⊨ (bct and f g) = (R , F , V ⊨ f) ∧ (R , F , V ⊨ g)
R , F , V ⊨ (bct imp f g) = (R , F , V ⊨ f) → (R , F , V ⊨ g)
R , F , V ⊨ (bct iff f g) = (R , F , V ⊨ f) ↔ (R , F , V ⊨ g)
R , F , V ⊨ (qtf false f) = ∀ (x) → (R , F , (V / 0 ↦ x) ⊨ f)
R , F , V ⊨ (qtf true f) = ∃ (λ x → (R , F , (V / 0 ↦ x) ⊨ f))
R , F , V ⊨ (rel r ts) = tr (R r (terms-val F V ts))

_=>_ : Form → Form → Set 
f => g = ∀ R F V → (R , F , V ⊨ bct imp f g)

standard : RA → Set 
standard R = ∀ d0 d1 → (tr (R (sf ('=' ∷ [])) (d0 ∷ d1 ∷ [])) ↔ (d0 ≡ d1))

in-prob : Form → Prob → Set
in-prob f P = ∃ (\ n → (n , f) ∈ P)

unsat-prob : Prob → Set
unsat-prob P = ∀ R F V → standard R → ∃ (λ f → ((in-prob f P) ∧ (¬ R , F , V ⊨ f)))

sats : RA → FA → VA → Prob → Bch → Set
sats R F V P B = ∀ f → ((in-prob f P) ∨ (f ∈ B)) → (R , F , V ⊨ f)

sat : Prob → Bch → Set
sat P B = ∃ λ R → ∃ λ F → ∃ λ V → (standard R ∧ sats R F V P B)

unsat : Prob → Bch → Set
unsat P B = ∀ R F V → standard R → ∃ (λ f → (((in-prob f P) ∨ (f ∈ B)) ∧ (¬ R , F , V ⊨ f)))

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

good-prob-nil : good-prob []
good-prob-nil k f (n , ()) 

data mono-fun : Nat → Nat → Form → Set where
  mono-fun-fa : ∀ k m f → mono-fun k (suc m) f → mono-fun k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-fun-eq : ∀ k m f → good-ftr (suc k) f → 
    mono-fun k m ((fun f (mono-args-lft m)) =* (fun f (mono-args-rgt m)))

data mono-rel : Nat → Nat → Form → Set where
  mono-rel-fa : ∀ k m f → mono-rel k (suc m) f → mono-rel k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-rel-imp : ∀ k m r → good-ftr (suc k) r → 
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
    choice k m ((∃* f) →* (subst-form 0 (skm-term-asc k m) f))
  choice-imp-desc : ∀ k m f → good-form k f → vars-lt-form (suc m) f → 
    choice k m ((∃* f) →* (subst-form 0 (skm-term-desc k m) f))

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

tri-eq-lt : ∀ {A : Set} {a b c : A} (k m : Nat) → (k < m) → (tri k a b c m) ≡ a 
tri-eq-lt {A} {a} {b} {c} k m h0 = 
  intro-ite-lem (k <n m) (λ x → x ≡ a) 
    (\ _ → refl) 
    (\ h1 → elim-bool-absurd (lt-to-nat-lt k m h0) h1)

tri-eq-eq : ∀ {A : Set} {a b c : A} (k m : Nat) → (k ≡ m) → (tri k a b c m) ≡ b 
tri-eq-eq {A} {a} {b} {c} k m h0 = 
  intro-ite-lem (k <n m) (λ x → x ≡ b) 
    (λ h1 → ⊥-elim (not-lt-self m (nat-lt-to-lt m m (eq-elim (λ x → tr (x <n m)) h0 h1)))) 
    \ h1 → intro-ite-lem (k =n m) (\ x → x ≡ b) (\ _ → refl) \ h2 → elim-bool-absurd (eq-to-nat-eq k m h0) h2

tri-eq-gt : ∀ {A : Set} {a b c : A} (k m : Nat) → (k > m) → (tri k a b c m) ≡ c 
tri-eq-gt {A} {a} {b} {c} k m h0 = 
  intro-ite-lem (k <n m) (λ x → x ≡ c) 
    (\ h1 → ⊥-elim (lt-to-not-gt _ _ h0 (nat-lt-to-lt _ _ h1))) 
    \ h1 → intro-ite-lem (k =n m) (λ x → x ≡ c) 
      (\ h2 → ⊥-elim (lt-to-not-eq _ _ h0 ( eq-symm (nat-eq-to-eq h2)))) 
      \ h2 → refl 

tri-elim : ∀ {A : Set} {a b c : A} (k m : Nat) → (P : A → Set) →
  (k < m → P a) → (k ≡ m → P b) → (k > m → P c) → P (tri k a b c m)
tri-elim k m P hl he hg = 
  intro-ite-lem (k <n m) P 
    (\ h0 → hl  (nat-lt-to-lt _ _ h0)) 
    \ h0 → intro-ite-lem (k =n m) P 
      (\ h1 → he (nat-eq-to-eq h1)) 
      \ h1 → (hg ( or-elim (trichotomy k m) 
        (\ h2 → elim-bool-absurd (lt-to-nat-lt _ _ h2) h0) 
        (or-elim' (\h3 → elim-bool-absurd (eq-to-nat-eq _ _ h3) h1) id) )) 

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
implies-a false  (bct and f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (fst h1) 
implies-a true (bct and f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (snd h1) 
implies-a false  (bct iff f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (fst h1) 
implies-a true (bct iff f0 f1) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (snd h1) 
implies-a false  (not (bct or f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (not-or-lft h1) 
implies-a true (not (bct or f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (not-or-rgt h1) 
implies-a false  (not (bct imp f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (not-imp-lft h1) 
implies-a true (not (bct imp f0 f1)) g h0 R F V h1 = 
  eq-elim (\ x → R , F , V ⊨ x) (just-inj h0) (not-imp-rgt h1) 

termoid-val-incr : ∀ b F V d (t : Termoid b) → termoid-val F (V / 0 ↦ d) (incr-var t) ≡ termoid-val F V t 
termoid-val-incr false F V d (var k) = refl
termoid-val-incr false F V d (fun f ts) = 
  cong (F f) (termoid-val-incr true F V d ts)
termoid-val-incr true  F V d nil = refl
termoid-val-incr true  F V d (cons t ts) = 
  cong-2 _∷_ 
    (termoid-val-incr false F V d t) 
    (termoid-val-incr true F V d ts)

term-val-incr : ∀ F V d t → term-val F (V / 0 ↦ d) (incr-var t) ≡ term-val F V t 
term-val-incr = termoid-val-incr false

update-update : ∀ V k d e → ((V / 0 ↦ e ) / (suc k) ↦ d) ≡ ((V / k ↦ d) / 0 ↦ e) 
update-update V k d e = FX _ _ \ { 0 → refl ; (suc m) → refl }

termoid-val-subst : ∀ (F : FA) (V : VA) (k : Nat) (b : Bool) (s : Term) (t : Termoid b) → 
  (termoid-val F (V / k ↦ term-val F V s) t) ≡ (termoid-val F V (subst-termoid k s t))
termoid-val-subst F V k true s nil = refl
termoid-val-subst F V k true s (cons t ts) = 
  cong-2 _∷_ (termoid-val-subst F V k false s t) 
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
  (∀ d → (R0 , F0 , (V0 / 0 ↦ d) ⊨ f0) ↔ (R1 , F1 , (V1 / 0 ↦ d) ⊨ f1)) →  
  ((R0 , F0 , V0 ⊨ qtf b f0) ↔ (R1 , F1 , V1 ⊨ qtf b f1))   
qtf-iff-qtf true h0 = ex-iff-ex h0
qtf-iff-qtf false h0 = fa-iff-fa h0

bct-iff-bct : ∀ b {R0 R1 F0 F1 V0 V1 f0 f1 g0 g1} → 
  ((R0 , F0 , V0 ⊨ f0) ↔ (R1 , F1 , V1 ⊨ f1)) →  
  ((R0 , F0 , V0 ⊨ g0) ↔ (R1 , F1 , V1 ⊨ g1)) →  
  ((R0 , F0 , V0 ⊨ bct b f0 g0) ↔ (R1 , F1 , V1 ⊨ bct b f1 g1)) 
bct-iff-bct or h0 h1 = or-iff-or h0 h1
bct-iff-bct and h0 h1 = and-iff-and h0 h1
bct-iff-bct imp h0 h1 = imp-iff-imp h0 h1
bct-iff-bct iff h0 h1 = iff-iff-iff h0 h1

holds-subst : ∀ R F V k t f → 
  ((R , F , (V / k ↦ (term-val F V t)) ⊨ f) ↔ (R , F , V ⊨ subst-form k t f))
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
        (\ x → ((R , F , x ⊨ f) ↔ (R , F , V / 0 ↦ d ⊨ subst-form (suc k) (incr-var t) f))) 
        (update-update V k (term-val F V t) d) 
        ( eq-elim 
            ( λ x → 
                (R , F , (V / 0 ↦ d) / suc k ↦ x ⊨ f) ↔ 
                  (R , F , V / 0 ↦ d ⊨ subst-form (suc k) (incr-var t) f) ) 
            (term-val-incr F V d t) 
            (holds-subst R F _ (suc k) (incr-var t) f) )

implies-c : ∀ t f g → break-c t f ≡ just g → f => g
implies-c t (qtf false f) g h0 R F V h1 = 
  let h2 = just-inj h0 in 
  let h3 = h1 (term-val F V t) in
  eq-elim (λ x → R , F , V ⊨ x) h2 (fst (holds-subst R F V 0 t f) h3)
implies-c t (not (qtf true f)) g h0 R F V h1 = 
  let h2 = just-inj h0 in 
  eq-elim (λ x → R , F , V ⊨ x) h2 
    λ h3 → h1 (term-val F V t , snd (holds-subst R F V 0 t f) h3)

from-chks-good-ftr : ∀ k f → tr (chk-good-ftr k f) → good-ftr k f
from-chks-good-ftr k (nf m) h = nat-lt-to-lt _ _ h
from-chks-good-ftr _ (sf _) _ = tt

chks-good : ∀ {b} k (t : Termoid b) → tr (chk-good-termoid k t) → good-termoid k t 
chks-good {true} _ nil _ = tt
chks-good {true} k (cons t ts) h0 = 
  chks-good _ _ (from-tr-bfst _ _ h0) , chks-good _ _ (from-tr-bsnd _ _ h0)
chks-good {false} k (var m) h0 = tt
chks-good {false} k (fun f ts) h0 =
  from-chks-good-ftr _ _ (from-tr-bfst _ _ h0) , 
  chks-good _ _ (from-tr-bsnd _ _ h0)

from-chks-good-form : ∀ k f → tr (chk-good-form k f) → good-form k f  
from-chks-good-form _ (cst _) _ = tt
from-chks-good-form k (bct _ f g) h0 =  
  (from-chks-good-form k f (from-tr-bfst _ _ h0)) , 
  (from-chks-good-form k g (from-tr-bsnd _ _ h0))
from-chks-good-form k (not f) h0 = from-chks-good-form k f h0
from-chks-good-form k (qtf _ f) h0 = from-chks-good-form k f h0
from-chks-good-form k (rel r ts) h0 = 
  from-chks-good-ftr _ r (from-tr-bfst _ _ h0) , 
  chks-good k ts (from-tr-bsnd _ _ h0) 

good-ftr-suc : ∀ k f → good-ftr k f → good-ftr (suc k) f
good-ftr-suc k (nf m) h = lt-to-lt-suc m k h
good-ftr-suc _ (sf _) _ = tt

good-termoid-suc : ∀ {b} k (f : Termoid b) → good-termoid k f → good-termoid (suc k) f
good-termoid-suc {false} _ (var _) _ = tt 
good-termoid-suc {false} k (fun f ts) h0 = 
  good-ftr-suc k f (fst h0) , good-termoid-suc k ts (snd h0) 
good-termoid-suc {true} _ nil _ = tt
good-termoid-suc {true} k (cons t ts) h0 = 
  good-termoid-suc _ t (fst h0) , good-termoid-suc k ts (snd h0)

good-form-suc : ∀ k f → good-form k f → good-form (suc k) f
good-form-suc k (cst _) h0 = tt 
good-form-suc k (rel r ts) h0 = 
   ( good-ftr-suc _ _ (fst h0) , 
     good-termoid-suc _ _ (snd h0) ) 
good-form-suc k (not f) h0 = good-form-suc k f h0
good-form-suc k (bct _ f g) h0 =
  (good-form-suc k f (fst h0)) , 
  (good-form-suc k g (snd h0))
good-form-suc k (qtf _ f) h0 = good-form-suc k f h0

good-bch-cons : ∀ f B → good-form (suc (length B)) f → good-bch B → good-bch (f ∷ B)
good-bch-cons f B h0 h1 g = 
  or-elim' (\ h2 → eq-elim _ (eq-symm h2) h0) (\ h2 → good-form-suc _ g (h1 _ h2)) 

prsv-implies : ∀ P B f g → f ∈ B → f => g → unsat P (g ∷ B) → unsat P B 
prsv-implies P B f g h0 h1 h2 R F V h3 = 
  ex-elim (h2 R F V h3) ( \ h h4 → let h5 = snd h4 
    in or-elim (fst h4) 
      (\ h6 → (h , (or-lft h6 , h5))) 
      \ h6 → or-elim h6 
        (\ h7 → (f , (or-rgt h0 , modus-tollens 
           (\ h8 → eq-elim (\ x → R , F , V ⊨ x) (eq-symm h7) 
             (h1 R F V h8))
          h5) ) ) 
        \ h7 → (h , (or-rgt h7 , h5)) )

prsv-a : ∀ P B b f g → f ∈ B → (break-a b f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-a P B b f g h0 h1 = prsv-implies P B f g h0 (implies-a _ _ _ h1) 

unsat-or-cons : ∀ P B f g → unsat P (f ∷ B) → unsat P (g ∷ B) → unsat P (bct or f g ∷ B)
unsat-or-cons P B f g hf hg R F V hs = ex-elim (hf R F V hs) \ f' h0 → 
  or-elim (fst h0) 
    (\ h1 → (f' , (or-lft h1 , snd h0))) 
    ( or-elim' 
      ( \ h2 → ex-elim (hg R F V hs) \ g' h3 → 
        or-elim (fst h3) 
          (\ h4 → (g' , (or-lft h4 , snd h3))) 
          ( or-elim' 
            ( \ h4 → ( bct or f g , 
              ( or-rgt (or-lft refl), 
                or-elim' 
                  (eq-elim (λ x → ¬ (R , F , V ⊨ x)) h2 (snd h0)) 
                  (eq-elim (λ x → ¬ (R , F , V ⊨ x)) h4 (snd h3)) ) ) ) 
            (\ h4 → (g' , (or-rgt (or-rgt h4) , snd h3))) )
      ) 
      (\ h1 → (f' , (or-rgt (or-rgt h1) , snd h0))) )

prsv-b : ∀ P B f g h → f ∈ B → (break-b f ≡ just (g , h)) → 
  unsat P (g ∷ B) → unsat P (h ∷ B) → unsat P B 
prsv-b P B f g h h0 h1 h2 h3 = prsv-implies P B f (bct or g h) 
  h0 (implies-b _ _ _ h1) (unsat-or-cons _ _ _ _ h2 h3)

prsv-c : ∀ P B t f g → f ∈ B → (break-c t f ≡ just g) → unsat P (g ∷ B) → unsat P B 
prsv-c P B t f g h1 h2 h3 = prsv-implies P B f g h1 (implies-c t f g h2) h3

sat-or-unsat : ∀ P B → (sat P B ∨ unsat P B)
sat-or-unsat P B = elim-lem (unsat P B) or-rgt λ h0 →  
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

term-val-update-par : ∀ F k d V → 
  term-val (F / nf k ↦f const-fun d) V (par k) ≡ d
term-val-update-par F k d V = 
  let h0 = tr-to-ite-eq {List D → D} {k =n k} {λ _ → d} {F (nf k)} (eq-to-nat-eq k k refl) in 
  eq-elim (λ x → x [] ≡ d) (eq-symm h0) refl 

from-break-n-eq-just : ∀ f g → break-n f ≡ just g → f ≡ (not (not g)) 
from-break-n-eq-just (not (not f)) g h0 = cong not (cong not (just-inj h0))

ftr-eq-to-eq : ∀ f g → tr (ftr-eq f g) → f ≡ g
ftr-eq-to-eq (nf k) (nf m) h0 = cong nf (nat-eq-to-eq h0)
ftr-eq-to-eq (sf s) (sf t) h0 = cong sf (chars-eq-to-eq  _ _ h0)

good-to-ftr-neq : ∀ k f → (good-ftr k f) → f ≠ nf k
good-to-ftr-neq k (nf m) h0 h1 = 
  ex-falso h0 (eq-elim (λ x → ¬ (m < x)) (nf-inj h1) (not-lt-self m))
good-to-ftr-neq k (sf m) _ ()

good-ftr-to-eq : ∀ k r R rl → (good-ftr k r) → (R / (nf k) ↦r rl) r ≡ R r
good-ftr-to-eq k r R rl h0 = 
  intro-ite-lem {Rel} (ftr-eq (nf k) r) (λ x → x ≡ R r) 
        ( λ h1 → 
            let h2 = ftr-eq-to-eq (nf k) r h1 in 
            let h3 = good-to-ftr-neq k r h0 in
            ex-falso (eq-symm h2) h3 ) 
        λ _ → refl 

good-to-termoid-val-eq : ∀ {b} F V k fn (t : Termoid b) → (good-termoid k t) → 
  (termoid-val (F / nf k ↦f fn) V t) ≡ (termoid-val F V t) 
good-to-termoid-val-eq {true} F V k fn nil h0 = refl
good-to-termoid-val-eq {true} F V k fn (cons t ts) h0 = 
  cong-2 _∷_
    (good-to-termoid-val-eq F V k fn t (fst h0))  
    (good-to-termoid-val-eq F V k fn ts (snd h0))
good-to-termoid-val-eq F V k fn (var m) h0 = refl
good-to-termoid-val-eq F V k fn (fun f ts) h0 = 
  cong-2 {Fun} {List D} {D} (λ x y → x y) {(F / nf k ↦f fn) f} {F f} 
    ( intro-ite-lem {Fun} (ftr-eq (nf k) f) (λ x → x ≡ F f) 
        ( λ h1 → 
            let h2 = eq-symm (ftr-eq-to-eq _ _ h1) in 
            let h3 : k < k  
                h3 = (fst (eq-elim {_} {f} {nf k} (λ x → good-termoid k (fun x ts)) h2 h0)) in
            ⊥-elim (not-lt-self k h3) ) 
        λ _ → refl )
    (good-to-termoid-val-eq F V k fn ts (snd h0))

good-to-holds-ru-iff : ∀ R F V k r f → good-form k f → 
  ((R / nf k ↦r r), F , V ⊨ f) ↔ (R , F , V ⊨ f)
good-to-holds-ru-iff R F V k r (cst b) _ = iff-refl
good-to-holds-ru-iff R F V k r (not f) h0 = 
  iff-to-not-iff-not (good-to-holds-ru-iff R F V k r f h0)
good-to-holds-ru-iff R F V k r (bct b f g) h0 = 
  bct-iff-bct b 
    (good-to-holds-ru-iff R F V k r f (fst h0)) 
    (good-to-holds-ru-iff R F V k r g (snd h0)) 
good-to-holds-ru-iff R F V k r (qtf b f) h0 = 
  qtf-iff-qtf b 
    λ d → good-to-holds-ru-iff R F _ k r f h0
good-to-holds-ru-iff R F V k rl (rel r ts) h0 = 
  eq-to-iff (λ (x : Rel) → tr (x (termoid-val F V ts))) ((R / (nf k) ↦r rl) r) (R r) 
    (good-ftr-to-eq k r R rl (fst h0))

good-to-holds-update-iff : ∀ R F V k fn f → good-form k f → 
  (R , (F / nf k ↦f fn), V ⊨ f) ↔ (R , F , V ⊨ f)
good-to-holds-update-iff R F V k fn (cst b) _ = iff-refl
good-to-holds-update-iff R F V k fn (not f) h0 = 
  iff-to-not-iff-not (good-to-holds-update-iff R F V k fn f h0)
good-to-holds-update-iff R F V k fn (bct b f g) h0 = 
  bct-iff-bct b 
    (good-to-holds-update-iff R F V k fn f (fst h0)) 
    (good-to-holds-update-iff R F V k fn g (snd h0)) 
good-to-holds-update-iff R F V k fn (qtf b f) h0 = 
  qtf-iff-qtf b 
    λ d → good-to-holds-update-iff R F _ k fn f h0
good-to-holds-update-iff R F V k fn (rel r ts) h0 = 
  eq-to-iff (λ x → tr (R r x)) _ _ (good-to-termoid-val-eq F V k fn ts (snd h0)) 
  
extend : List D → VA 
extend [] _ = wit
extend (d ∷ _) 0 = d
extend (_ ∷ ds) (suc k) = extend ds k

def-rl-asc : RA → FA → Form → Rel
def-rl-asc R F f ds = rt (R , F , extend ds ⊨ f)

def-rl-desc : RA → FA → Form → Rel
def-rl-desc R F f ds = def-rl-asc R F f (reverse ds)

skm-fun-asc : RA → FA → Form → Fun
skm-fun-asc R F f ds = 
  elim-lem (R , F , extend ds ⊨ ∃* f) 
    (ex-elim' (λ d _ → d)) 
    (λ _ → wit)

skm-fun-desc : RA → FA → Form → Fun
skm-fun-desc R F f ds = skm-fun-asc R F f (reverse ds) 

trunc : Nat → VA → List D
trunc 0 _ = []
trunc (suc k) V = V 0 ∷ trunc k (↓ V)

extend-skm-fun-asc-holds : ∀ R F f ds → (R , F , extend ds ⊨ ∃* f) → 
  R , F , (extend ds) / 0 ↦ (skm-fun-asc R F f ds) ⊨ f  
extend-skm-fun-asc-holds R F f ds h0 = 
  intro-elim-lem-yes (λ x → R , F , extend ds / 0 ↦ x ⊨ f) 
    (λ (d , h1) → h1) 
    h0 

extend-skm-fun-desc-reverse-holds : ∀ R F f ds → (R , F , extend ds ⊨ ∃* f) → 
  R , F , (extend ds) / 0 ↦ (skm-fun-desc R F f (reverse ds)) ⊨ f  
extend-skm-fun-desc-reverse-holds R F f ds h0 = 
  let h1 = extend-skm-fun-asc-holds R F f ds h0 in 
  eq-elim-symm (λ x → R , F , extend ds / 0 ↦ skm-fun-asc R F f x ⊨ f) (reverse-reverse ds) h1 

eq-va-lt : Nat → VA → VA → Set
eq-va-lt k V0 V1 = ∀ m → m < k → V0 m ≡ V1 m

eq-va-lt-suc : ∀ k V0 V1 d0 d1 → eq-va-lt k V0 V1 → d0 ≡ d1 → 
  eq-va-lt (suc k) (V0 / 0 ↦ d0) (V1 / 0 ↦ d1)
eq-va-lt-suc k V0 V1 d0 d1 h0 h1 0 h2 = h1
eq-va-lt-suc k V0 V1 d0 d1 h0 h1 (suc m) (suc< _ _ h2) = h0 m h2

eq-va-lt-to-eq : ∀ {b} F V0 V1 k (t : Termoid b) → eq-va-lt k V0 V1 → vars-lt-termoid k t → 
  (termoid-val F V0 t) ≡ (termoid-val F V1 t) 
eq-va-lt-to-eq {true} F V0 V1 k nil _ _ = refl
eq-va-lt-to-eq {true} F V0 V1 k (cons t ts) h0 h1 = 
  cong-2 _∷_ (eq-va-lt-to-eq F V0 V1 k t h0 (fst h1)) (eq-va-lt-to-eq F V0 V1 k ts h0 (snd h1))
eq-va-lt-to-eq {false} F V0 V1 k (var m) h0 h1 = h0 m h1
eq-va-lt-to-eq {false} F V0 V1 k (fun f ts) h0 h1 = cong (F f) (eq-va-lt-to-eq F V0 V1 k ts h0 h1)

eq-va-lt-to-iff : ∀ R F V0 V1 k f → eq-va-lt k V0 V1 → vars-lt-form k f → 
  (R , F , V0 ⊨ f) ↔ (R , F , V1 ⊨ f) 
eq-va-lt-to-iff R F V0 V1 k (cst b) _ _ = iff-refl
eq-va-lt-to-iff R F V0 V1 k (not f) h0 h1 = iff-to-not-iff-not (eq-va-lt-to-iff R F V0 V1 k f h0 h1)
eq-va-lt-to-iff R F V0 V1 k (bct b f g) h0 h1 = 
  bct-iff-bct b (eq-va-lt-to-iff R F V0 V1 k f h0 (fst h1)) (eq-va-lt-to-iff R F V0 V1 k g h0 (snd h1))
eq-va-lt-to-iff R F V0 V1 k (qtf b f) h0 h1 = 
  qtf-iff-qtf b λ d → eq-va-lt-to-iff R F _ _ (suc k) f (eq-va-lt-suc k V0 V1 d d h0 refl) h1
eq-va-lt-to-iff R F V0 V1 k (rel r ts) h0 h1 = 
  eq-to-iff (λ x → tr (R r x)) (terms-val F V0 ts) _ (eq-va-lt-to-eq F V0 V1 k ts h0 h1)

eq-va-lt-extend-trunc : ∀ V k → eq-va-lt k (extend (trunc k V)) V
eq-va-lt-extend-trunc V 0 m ()
eq-va-lt-extend-trunc V (suc k ) 0 (0< _) = refl
eq-va-lt-extend-trunc V (suc k ) (suc m) (suc< _ _ h0) = eq-va-lt-extend-trunc (↓ V) k m h0

holds-extend-trunc-iff : ∀ R F V k f → vars-lt-form k f →  
  (R , F , extend (trunc k V) ⊨ f) ↔ (R , F , V ⊨ f)
holds-extend-trunc-iff R F V k f h0 = eq-va-lt-to-iff R F (extend (trunc k V)) V k f (eq-va-lt-extend-trunc V k) h0
  
fa-update-eq : ∀ F k fn → fn ≡ (F / nf k ↦f fn) (nf k) 
fa-update-eq F k fn = eq-symm (tr-to-ite-eq {_} {ftr-eq (nf k) (nf k)} (eq-to-nat-eq k k refl)) 
 
ra-update-eq : ∀ R k r → (R / nf k ↦r r) (nf k) ≡ r
ra-update-eq R k r = (tr-to-ite-eq {_} {ftr-eq (nf k) (nf k)} (eq-to-nat-eq k k refl)) 

ru-sf-eq : ∀ R k r s → (R / nf k ↦r r) (sf s) ≡ R (sf s)
ru-sf-eq R k r s = fs-to-ite-ne {Rel} {ftr-eq (nf k) (sf s)} {r} tt

reverse-trunc-eq-termoid-val-vars-desc-core : ∀ F V m → 
  termoid-val F (↓ V) (vars-desc m) ∷ʳ V 0 ≡ termoid-val F V (cons (var m) (vars-desc m))
reverse-trunc-eq-termoid-val-vars-desc-core F V 0 = refl 
reverse-trunc-eq-termoid-val-vars-desc-core F V (suc m) = cong-2 _∷_ refl (reverse-trunc-eq-termoid-val-vars-desc-core F _ m) 

termoid-val-rev-terms : ∀ F V ts0 ts1 → 
  termoid-val F V (rev-terms ts0 ts1) ≡  reverseAcc (termoid-val F V ts1) (termoid-val F V ts0) 
termoid-val-rev-terms F V nil ts1 = refl 
termoid-val-rev-terms F V (cons t ts0) ts1 = termoid-val-rev-terms F V ts0 (cons t ts1) 

reverse-trunc-eq-termoid-val-vars-desc : ∀ F V m → reverse (trunc m V) ≡ termoid-val F V (vars-desc m)
reverse-trunc-eq-termoid-val-vars-desc F V 0 = refl
reverse-trunc-eq-termoid-val-vars-desc F V (suc m) = eq-trans _ (reverse-cons (V 0) (trunc m (↓ V))) 
  (eq-trans ((termoid-val F (↓ V) (vars-desc m)) ∷ʳ V 0) 
  (cong (λ x → x ∷ʳ V 0) (reverse-trunc-eq-termoid-val-vars-desc F (↓ V) m)) (reverse-trunc-eq-termoid-val-vars-desc-core F _ m))

trunc-eq-termoid-val-vars-asc : ∀ F V m → (trunc m V) ≡ termoid-val F V (vars-asc m)
trunc-eq-termoid-val-vars-asc F V m = 
  reverse-inj _ _ 
    ( eq-trans _ (reverse-trunc-eq-termoid-val-vars-desc F V m) 
        ( eq-trans _
            (eq-symm (reverse-reverse (termoid-val F V (vars-desc m)))) 
            ( cong reverse {_} {termoid-val F V (vars-asc m)} 
                (eq-symm (termoid-val-rev-terms F V (vars-desc m) nil)) ) ) )

good-rev-terms : ∀ k ts0 ts1 → good-terms k ts0 → good-terms k ts1 → good-terms k (rev-terms ts0 ts1)
good-rev-terms k nil ts1 _ h0 = h0 
good-rev-terms k (cons t ts0) ts1 (h0 , h1) h2 = good-rev-terms k ts0 (cons t ts1) h1 (h0 , h2) 

good-vars-desc : ∀ k m → good-termoid k (vars-desc m) 
good-vars-desc k 0 = tt
good-vars-desc k (suc m) = tt , (good-vars-desc _ _)

good-vars-asc : ∀ k m → good-termoid k (vars-asc m) 
good-vars-asc k m = good-rev-terms k (vars-desc m) nil (good-vars-desc _ _) tt

data only-vars : ∀ {b} → Termoid b → Set where 
  only-vars-nil : only-vars nil
  only-vars-var : ∀ k → only-vars (var k)
  only-vars-cons : ∀ t ts → only-vars t → only-vars ts → only-vars (cons t ts)

only-vars-to-eq : ∀ {b} F0 F1 V (t : Termoid b) → only-vars t → termoid-val F0 V t ≡ termoid-val F1 V t
only-vars-to-eq F0 F1 V nil _ = refl
only-vars-to-eq F0 F1 V (var _) _ = refl
only-vars-to-eq F0 F1 V (cons t ts) (only-vars-cons _ _ h0 h1) = 
  cong-2 _∷_ (only-vars-to-eq _ _ _ t h0) (only-vars-to-eq _ _ _ ts h1)

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

skm-fun-asc-trunc : ∀ R F V f k m →
  skm-fun-asc R F f (trunc m V) ≡
    term-val (F / nf k ↦f skm-fun-asc R F f) V (skm-term-asc k m)
skm-fun-asc-trunc R F V f k m = 
  eq-trans _ 
    (cong (skm-fun-asc R F f) {trunc m V} (trunc-eq-termoid-val-vars-asc F V m))
    ( cong-fun-arg {_} {_} {skm-fun-asc R F f} {_} 
        {termoid-val F V (vars-asc m)} {termoid-val _ V (vars-asc m)} 
        (fa-update-eq F k _) 
        (val-vars-asc-eq _ _ V m) )

skm-fun-desc-reverse-trunc : ∀ R F V f k m →
  skm-fun-desc R F f (reverse (trunc m V)) ≡
    term-val (F / nf k ↦f skm-fun-desc R F f) V (skm-term-desc k m)
skm-fun-desc-reverse-trunc R F V f k m = 
  eq-trans _ 
    (cong (skm-fun-desc R F f) {reverse (trunc m V)} (reverse-trunc-eq-termoid-val-vars-desc F V m))
    ( cong-fun-arg {_} {_} {skm-fun-desc R F f} {_} 
        {termoid-val F V (vars-desc m)} {termoid-val _ V (vars-desc m)} 
        (fa-update-eq F k _) (val-vars-desc-eq _ _ V m) ) 

eq-va-lt-symm : ∀ k V0 V1 → eq-va-lt k V0 V1 → eq-va-lt k V1 V0 
eq-va-lt-symm k V0 V1 h0 m h1 = eq-symm (h0 m h1)

skm-fun-asc-aux : ∀ R F V k m f → good-form k f → 
  vars-lt-form (suc m) f → (R , F , V ⊨ ∃* f) → 
  R , (F / (nf k) ↦f skm-fun-asc R F f) , V ⊨ subst-form 0 (skm-term-asc k m) f
skm-fun-asc-aux R F V k m f hf h0 h1 = 
  fst (holds-subst R _ V 0 (skm-term-asc k m) f) 
    (
      let h2 : R , F , extend (trunc m V) ⊨ ∃* f 
          h2 = fst (eq-va-lt-to-iff  R F _ (extend (trunc m V)) m (∃* f) (eq-va-lt-symm _ _ _ (eq-va-lt-extend-trunc V m)) h0) h1 in
      let h3 = extend-skm-fun-asc-holds R F f (trunc m V) h2 in 
      snd (good-to-holds-update-iff R F _ k _ f hf) 
       ( fst 
            ( eq-va-lt-to-iff R F _ _ (suc m) f 
                (eq-va-lt-suc m _ _ _ _ (eq-va-lt-extend-trunc V m)  (skm-fun-asc-trunc R F V f k m))
                h0 ) h3 )
   ) 

skm-fun-desc-aux : ∀ R F V k m f → good-form k f → 
  vars-lt-form (suc m) f → (R , F , V ⊨ ∃* f) → 
  R , (F / (nf k) ↦f skm-fun-desc R F f) , V ⊨ subst-form 0 (skm-term-desc k m) f
skm-fun-desc-aux R F V k m f hf h0 h1 = 
  fst (holds-subst R _ V 0 (skm-term-desc k m) f) 
    (
      let h2 : R , F , extend (trunc m V) ⊨ ∃* f 
          h2 = fst (eq-va-lt-to-iff  R F _ (extend (trunc m V)) m (∃* f) (eq-va-lt-symm _ _ _ (eq-va-lt-extend-trunc V m)) h0) h1 in
      let h3 = extend-skm-fun-desc-reverse-holds R F f (trunc m V) h2 in 
      snd (good-to-holds-update-iff R F _ k _ f hf) 
        ( fst 
            ( eq-va-lt-to-iff R F _ _ (suc m) f 
                (eq-va-lt-suc m _ _ _ _ (eq-va-lt-extend-trunc V m)  (skm-fun-desc-reverse-trunc R F V f k m))
                h0 ) h3 )
    )

prsv-t-pred-def : ∀ R F k m f → pred-def k m f → ∃ λ rl → ∀ V → (R / (nf k) ↦r rl) , F , V ⊨ f 
prsv-t-pred-def R F k m _ (pred-def-fa k m f h0) = 
  ex-elim (prsv-t-pred-def R F k (suc m) f h0) λ r h1 → r , λ V d → h1 _
prsv-t-pred-def R F k m _ (pred-def-iff-asc k m f h0 h1) = 
  def-rl-asc R F f , λ V → iff-trans (tr (def-rl-asc R F f ((trunc m V)))) 
    ( eq-to-iff-2 (λ x y → tr (x y)) ((R / (nf k) ↦r _) (nf k)) (def-rl-asc R F f) _ (trunc m V) 
        (ra-update-eq R k _) (eq-symm (trunc-eq-termoid-val-vars-asc F V m)) ) 
    (iff-trans _ (tr-rt-iff) (iff-trans (R , F , V ⊨ f) 
  (holds-extend-trunc-iff R F V m f h1) (iff-symm  (good-to-holds-ru-iff R F V k  _ f h0))))
prsv-t-pred-def R F k m _ (pred-def-iff-desc k m f h0 h1) = 
  def-rl-desc R F f , λ V → iff-trans (tr (def-rl-desc R F f (reverse (trunc m V)))) 
    (eq-to-iff-2 (λ x y → tr (x y)) ((R / nf k ↦r _) (nf k))
      (def-rl-desc R F f) _ (reverse (trunc m V)) (ra-update-eq R k _) 
        (eq-symm (reverse-trunc-eq-termoid-val-vars-desc F V m))) (iff-trans _ tr-rt-iff 
          (iff-trans (R , F , extend (trunc m V) ⊨ f) 
            (eq-to-iff (λ x → R , F , extend x ⊨ f) _ (trunc m V) (reverse-reverse _)) 
            (iff-trans (R , F , V ⊨ f) (holds-extend-trunc-iff R F V m f h1) 
              ((iff-symm  (good-to-holds-ru-iff R F V k  _ f h0))))))

prsv-t-choice : ∀ R F k m f → choice k m f → ∃ λ fn → ∀ V → R , F / (nf k) ↦f fn , V ⊨ f 
prsv-t-choice R F k m _ (choice-fa k m f h0) = 
  ex-elim (prsv-t-choice R F k (suc m) f h0) λ fn h1 → fn , λ V d → h1 (V / 0 ↦ d)
prsv-t-choice R F k m _ (choice-imp-asc k m f h0 h1) = 
  skm-fun-asc R F f , λ V h2 → 
    let h3 : R , F , V ⊨ ∃* f 
        h3 = fst (good-to-holds-update-iff R F V k _ (∃* f) h0) h2 in 
    skm-fun-asc-aux R _ V k m f h0 h1 h3 
prsv-t-choice R F k m _ (choice-imp-desc k m f h0 h1) = 
  skm-fun-desc R F f , λ V h2 → 
    let h3 : R , F , V ⊨ ∃* f 
        h3 = fst (good-to-holds-update-iff R F V k _ (∃* f) h0) h2 in 
    skm-fun-desc-aux R _ V k m f h0 h1 h3 

prsv-d-aux : ∀ R F V k f g → good-form k f → break-d k f ≡ just g → 
  R , F , V ⊨ f → ∃ λ d → R , F / (nf k) ↦f (const-fun d) , V ⊨ g 
prsv-d-aux R F V k (qtf true f) g h0 h1 h2 = 
  ex-elim h2 λ d h3 → let F' = (F / (nf k) ↦f (const-fun d)) in 
    d , eq-elim (λ x → R , F' , V ⊨ x) (just-inj h1)
      ( fst (holds-subst R F' V 0 (par k) f) 
        ( eq-elim (λ x → R , F' , V / 0 ↦ x ⊨ f) 
          ( eq-symm (term-val-update-par F k d V)) 
            (snd (good-to-holds-update-iff _ _ _ _ _ f h0) h3) ) )
prsv-d-aux R F V k (not (qtf false f)) g h0 h1 h2 = 
  let h2' = not-fa-to-ex-not _ h2 in 
  ex-elim h2' λ d h3 → let F' = (F / (nf k) ↦f (const-fun d)) in 
    d , eq-elim (λ x → R , F' , V ⊨ x) (just-inj h1) λ hc → h3 
     let h4 = snd (holds-subst R F' V 0 (par k) f) hc in 
     let h5 = fst (good-to-holds-update-iff R F _ k (const-fun d) f h0) h4 in 
     eq-elim (λ x → R , F , V / 0 ↦ x ⊨ f) (term-val-update-par F k d V) h5

sats-to-sats : ∀ P B R F V fn f → good-prob P → good-bch B → 
  (R , F / (nf (length B)) ↦f fn , V ⊨ f) → sats R F V P B → sats R (F / (nf (length B)) ↦f fn) V P (f ∷ B)  
sats-to-sats P B R F V fn f h0 h1 h2 h3 g (or-lft h4) = 
  snd (good-to-holds-update-iff R F V (length B) fn g (h0 g _ h4)) (h3 g (or-lft h4))
sats-to-sats P B R F V fn f h0 h1 h2 h3 g (or-rgt (or-lft h4)) = 
  eq-elim (λ x → R , _ , V ⊨ x) (eq-symm h4) h2
sats-to-sats P B R F V fn f h0 h1 h2 h3 g (or-rgt (or-rgt h4)) = 
  snd (good-to-holds-update-iff R F V (length B) fn g (h1 g h4)) (h3 g (or-rgt h4))

sats-to-sats-ra : ∀ P B R F V rl f → good-prob P → good-bch B → 
  ((R / nf (length B) ↦r rl) , F , V ⊨ f) → sats R F V P B → sats (R / (nf (length B)) ↦r rl) F V P (f ∷ B)  
sats-to-sats-ra P B R F V rl f h0 h1 h2 h3 g (or-lft h4) = 
   snd (good-to-holds-ru-iff R F V (length B) rl g (h0 g _ h4)) (h3 g (or-lft h4))
sats-to-sats-ra P B R F V rl f h0 h1 h2 h3 g (or-rgt (or-lft h4)) = 
  eq-elim (λ x → _ , F , V ⊨ x) (eq-symm h4) h2
sats-to-sats-ra P B R F V rl f h0 h1 h2 h3 g (or-rgt (or-rgt h4)) =
  snd (good-to-holds-ru-iff R F V (length B) rl g (h1 g h4)) (h3 g (or-rgt h4))

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
                  F / (nf (length B)) ↦f (const-fun d) , 
                    V , h0 , sats-to-sats P B R F V (const-fun d) g hP hB h2 h1 ) )

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
                              ex-falso { R , F , V ⊨ g } 
                                (dne (eq-elim (λ x → ¬ (R , F , V ⊨ x)) h6 h3)) 
                                (eq-elim (λ x → ¬ (R , F , V ⊨ x)) h9 h5) ) 
                          (λ h8 → f1 , or-rgt h8 , h5) ) ) 
                (λ h6 → f0 , or-rgt h6 , h3) ) 

standard-to-holds : Form → Set 
standard-to-holds f = ∀ R F V → standard R → R , F , V ⊨ f

standard-to-holds-refl : standard-to-holds refl-axiom
standard-to-holds-refl R F V hR d = snd (hR d d) refl

standard-to-holds-symm : standard-to-holds symm-axiom
standard-to-holds-symm R F V hR d0 d1 h0 = 
  snd (hR d1 d0) (eq-symm (fst (hR d0 d1) h0))

standard-to-holds-trans : standard-to-holds trans-axiom
standard-to-holds-trans R F V hR d0 d1 d2 h0 h1 = 
  snd (hR d0 d2) (eq-trans d1 (fst (hR d0 d1) h0) (fst (hR d1 d2) h1))

mono-args-equal' : Nat → VA → Set
mono-args-equal' k V = ∀ m → m < k → V (suc (m * 2)) ≡ V (m * 2)

from-mono-args-equal-suc : ∀ V k → 
  mono-args-equal' (suc k) V → mono-args-equal' k V 
from-mono-args-equal-suc V k h0 m h1 = h0 m (lt-to-lt-suc m k h1) 

from-mono-args-equal-0 : ∀ F V k → mono-args-equal' k V → 
  (terms-val F V (mono-args-lft k) ≡ terms-val F V (mono-args-rgt k)) 
from-mono-args-equal-0 F V 0 _ = refl
from-mono-args-equal-0 F V (suc k) h0 = 
  cong-2 _∷_ (h0 k (lt-suc-self k)) 
    (from-mono-args-equal-0 F V k (from-mono-args-equal-suc V k h0)) 

from-mono-args-equal-1 : ∀ V k d → mono-args-equal' k V → 
  mono-args-equal' (suc k) ((V / 0 ↦ d) / 0 ↦ d) 
from-mono-args-equal-1 V k d h0 0 h1 = refl
from-mono-args-equal-1 V k d h0 (suc m) (suc< _ _ h1) = h0 m h1

holds-mono-fun : ∀ R F V k m f → standard R → 
  mono-args-equal' m V → mono-fun k m f → R , F , V ⊨ f 
holds-mono-fun R F V k m _ hR hE (mono-fun-fa k m f h0) d0 d1 h1 = 
  holds-mono-fun R F _ k (suc m) f hR 
    ( let h2 : d0 ≡ d1 
          h2 = (fst (hR d0 d1) h1) in 
      eq-elim (λ x → mono-args-equal' (suc m) ((V / 0 ↦ d0) / 0 ↦ x)) 
        h2 ((from-mono-args-equal-1 V m d0 hE)))
    h0
holds-mono-fun R F V k m _ hR hE (mono-fun-eq k m f _) = 
  snd (hR _ _) (cong (F f) (from-mono-args-equal-0 F V m hE))

holds-mono-rel : ∀ R F V k m f → standard R → 
  mono-args-equal' m V → mono-rel k m f → R , F , V ⊨ f 
holds-mono-rel R F V k m _ hR hE (mono-rel-fa k m f h0) d0 d1 h1 = 
  holds-mono-rel R F _ k (suc m) f hR 
    ( let h2 : d0 ≡ d1 
          h2 = (fst (hR d0 d1) h1) in 
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
                ex-falso (eq-elim (λ x → R , F , V ⊨ x) (eq-symm h4) (h0 R F V hR)) 
                  h3 ) 
            or-rgt ) , 
      h3

standard-ru : ∀ R k rl → standard R → standard (R / (nf k) ↦r rl)
standard-ru R k rl h0 d0 d1 = 
  eq-elim (λ x → tr (x _) ↔ (d0 ≡ d1)) (eq-symm (ru-sf-eq R k rl _)) (h0 _ _)

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
  sat-to-sat-to-unsat-to-unsat (ex-elim-3' λ R F V (h1 , h2 ) → 
    ex-elim (prsv-t-pred-def R F (length B) 0 f h0) (λ rl h3 → 
      (R / nf (length B) ↦r rl) , F , V , standard-ru R k rl h1 , (sats-to-sats-ra P B R F V rl f hP hB (h3 V) h2)))

prsv-good-b : ∀ f g h k → (break-b f ≡ just (g , h)) → good-form k f → 
  (good-form k g ∧ good-form k h)
prsv-good-b (bct or f0 f1) g h k h0 h1 =
  ( (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) (fst h1)) , 
    (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (snd h1)) )
prsv-good-b (bct imp f0 f1) g h k h0 h1 = 
  ( (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) (fst  h1)) , 
    (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (snd h1)) )
prsv-good-b (not (bct and f0 f1)) g h k h0 h1 = 
  (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) (fst  h1)) , 
  (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (snd h1)) 
prsv-good-b (not (bct iff f0 f1)) g h k h0 h1 = 
  (eq-elim (good-form k) (prod-inj-lft  (just-inj h0)) h1) , 
  (eq-elim (good-form k) (prod-inj-rgt (just-inj h0)) (and-symm h1)) 

good-subst-termoid : ∀ {b} s (t : Termoid b) k m → good-term k s → 
  good-termoid k t → good-termoid k (subst-termoid m s t)
good-subst-termoid {true} _ nil _ _ _ _ = tt
good-subst-termoid {true} s (cons t ts) k m h0 h1 = 
  (good-subst-termoid s _ _ _ h0 (fst h1)) ,
  (good-subst-termoid s _ _ _ h0 (snd h1)) 
good-subst-termoid {false} s (var n) k m h0 h1 = 
  tri-elim m n (good-termoid k) (\ _ → tt) (\ _ → h0) (\ _ → tt)
good-subst-termoid {false} s (fun f ts) k m h0 h1 = 
  (fst h1) , (good-subst-termoid _ ts k m h0 (snd h1))

good-subst-terms : ∀ t ts k m → good-term k t → 
  good-terms k ts → good-terms k (subst-terms m t ts)
good-subst-terms = good-subst-termoid 

good-incr-var : ∀ {b} k (t : Termoid b) → good-termoid k t → good-termoid k (incr-var t)
good-incr-var _ nil _ = tt
good-incr-var k (cons t ts) h = 
  (good-incr-var _ t (fst h)) , (good-incr-var _ ts (snd h))
good-incr-var k (var _) _ = tt
good-incr-var k (fun f ts) h = 
  fst h , (good-incr-var _ ts (snd h))

good-subst-form : ∀ t f k m → good-term k t → good-form k f → good-form k (subst-form m t f)
good-subst-form t (cst _) _ _ _ _ = tt
good-subst-form t (rel r ts) k m h0 h1 = 
  fst h1 , good-subst-terms t ts k m h0 (snd h1)
good-subst-form t (not f) = good-subst-form t f
good-subst-form t (bct _ f g) k m h0 h1 = 
  (good-subst-form t f k m h0 (fst h1)) , (good-subst-form t g k m h0 (snd h1))
good-subst-form t (qtf _ f) k m h0 h1 = 
  good-subst-form (incr-var t) f k (suc m) (good-incr-var _ _ h0) h1

good-term-par : ∀ k → good-term (suc k) (par k)
good-term-par k = (lt-suc-self _) , tt

prsv-good-d : ∀ f g k → good-form k f → (break-d k f ≡ just g) → good-form (suc k) g

prsv-good-d (qtf true f) g k h0 h1 = 
  eq-elim (good-form (suc k)) (just-inj h1) (good-subst-form (par k) 
    f _ _  (good-term-par k) (good-form-suc k f h0))
prsv-good-d (not (qtf false f)) g k h0 h1 = 
  eq-elim (good-form (suc k)) (just-inj h1) (good-subst-form (par k) 
    f _ _  (good-term-par k) (good-form-suc k f h0))

prsv-good-c : ∀ t f g k → good-term k t → good-form k f → (break-c t f ≡ just g) → good-form k g
prsv-good-c t (qtf false f) g k h0 h1 h2 = 
  eq-elim (good-form k) (just-inj h2) (good-subst-form t f _ _ h0 h1)
prsv-good-c t (not (qtf true f)) g k h0 h1 h2 = 
  eq-elim (good-form k) (just-inj h2) (good-subst-form t f k 0 h0 h1) 

prsv-good-a : ∀ b f g k → (break-a b f ≡ just g) → good-form k f → good-form k g
prsv-good-a false  (bct and f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (fst h1)
prsv-good-a true (bct and f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (snd h1)
prsv-good-a false  (bct iff f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) h1 --h1
prsv-good-a true (bct iff f0 f1) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (and-symm h1)
prsv-good-a false  (not (bct or f0 f1))  g k h0 h1 = eq-elim (good-form k) (just-inj h0) (fst h1) 
prsv-good-a true (not (bct or f0 f1))  g k h0 h1 = eq-elim (good-form k) (just-inj h0) (snd h1) 
prsv-good-a false  (not (bct imp f0 f1)) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (fst h1) 
prsv-good-a true (not (bct imp f0 f1)) g k h0 h1 = eq-elim (good-form k) (just-inj h0) (snd h1) 

good-mono-args-lft : ∀ k m → good-termoid k (mono-args-lft m)
good-mono-args-lft k 0 = tt
good-mono-args-lft k (suc m) = tt , (good-mono-args-lft k m)

good-mono-args-rgt : ∀ k m → good-termoid k (mono-args-rgt m)
good-mono-args-rgt k 0 = tt
good-mono-args-rgt k (suc m) = tt , good-mono-args-rgt k m

good-mono-fun : ∀ k m f → mono-fun k m f → good-form (suc k) f
good-mono-fun k m _ (mono-fun-fa k m f h0) = (tt , (tt , (tt , tt))) , (good-mono-fun k _ f h0) 
good-mono-fun k m _ (mono-fun-eq k m f h0) = tt , ((h0 , good-mono-args-lft _ _) , (h0 , good-mono-args-rgt _ _) , tt)

good-mono-rel : ∀ k m f → mono-rel k m f → good-form (suc k) f
good-mono-rel k m _ (mono-rel-fa k m f h0) = (tt , (tt , (tt , tt))) , (good-mono-rel k _ f h0) 
good-mono-rel k m _ (mono-rel-imp k m f h0) = (h0 , good-mono-args-lft _ _) , (h0 , good-mono-args-rgt  _ _)

good-choice : ∀ k m f → choice k m f → good-form (suc k) f
good-choice k m _ (choice-fa k m f h0) = good-choice k _ f h0
good-choice k m _ (choice-imp-asc k m f h0 h1) = (good-form-suc _ f h0) , 
  (good-subst-form (skm-term-asc k m) f (suc k) 0 ((lt-suc-self _) , good-vars-asc _ m) (good-form-suc  _ f h0))
good-choice k m _ (choice-imp-desc k m f h0 h1) = (good-form-suc _ f h0) , 
  ((good-subst-form (skm-term-desc k m) f (suc k) 0 ((lt-suc-self _) , good-vars-desc _ m) (good-form-suc  _ f h0)))

good-pred-def : ∀ k m f → pred-def k m f → good-form (suc k) f
good-pred-def k m _ (pred-def-fa k m f h0) = good-pred-def k _ f h0
good-pred-def k m _ (pred-def-iff-asc k m f h0 h1) = ((lt-suc-self _) , (good-vars-asc _ m)) , (good-form-suc _ f h0)
good-pred-def k m _ (pred-def-iff-desc k m f h0 h1) = 
 ((lt-suc-self _) , (good-vars-desc _ m)) , (good-form-suc _ f h0)

good-bch-t : ∀ B g → jst (length B) g → good-bch B → good-bch (g ∷ B)
good-bch-t B _ (jst-top _) h1           = good-bch-cons _ B tt h1
good-bch-t B _ (jst-not-bot _) h1       = good-bch-cons _ B tt h1
good-bch-t B _ (jst-refl _) h1          = good-bch-cons _ B (tt , tt , tt , tt) h1
good-bch-t B _ (jst-symm k) h1          = good-bch-cons _ B ((tt , (tt , (tt , tt))) , (tt , (tt , (tt , tt)))) h1
good-bch-t B _ (jst-trans k) h1         = good-bch-cons _ B ((tt , (tt , (tt , tt))) , ((tt , (tt , (tt , tt))) , (tt , (tt , (tt , tt))))) h1
good-bch-t B _ (jst-fun k f h0) h1      = good-bch-cons _ B (good-mono-fun k 0 f h0) h1
good-bch-t B _ (jst-rel k f h0) h1      = good-bch-cons _ B (good-mono-rel k 0 f h0) h1
good-bch-t B _ (jst-choice k f h0) h1   = good-bch-cons _ B (good-choice (length B) 0 _ h0) h1
good-bch-t B _ (jst-pred-def k f h0) h1 = good-bch-cons _ B (good-pred-def (length B) 0 _ h0) h1

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
  ( good-bch-cons _ _ (good-form-suc _ g (fst  (prsv-good-b _ _ _ _ h1 (h2 f h0)))) h2 , 
    good-bch-cons _ _ (good-form-suc _ h (snd (prsv-good-b _ _ _ _ h1 (h2 f h0)))) h2 )

good-bch-c : ∀ B t f g → good-term (suc (length B)) t → 
  f ∈ B → (break-c t f ≡ just g) → good-bch B → good-bch (g ∷ B) 
good-bch-c B t f g h0 h1 h2 h3 = good-bch-cons _ _ 
  (prsv-good-c t f g (suc (length B)) h0 (good-form-suc _ f (h3 _ h1)) h2)  h3

good-bch-d : ∀ B f g → f ∈ B → (break-d (length B) f ≡ just g) → good-bch B → good-bch (g ∷ B) 
good-bch-d B f g h0 h1 h2 = good-bch-cons g B (prsv-good-d f g (length B) (h2 f h0) h1) h2

cont-inj-val : ∀ {A : Set} {a0 a1 : A} {st0 st1} → 
  cont a0 st0 ≡ cont a1 st1 → a0 ≡ a1 
cont-inj-val refl = refl

is-cont : ∀ {A : Set} → Res A → Set
is-cont (stop _) = ⊥
is-cont (cont _ _) = ⊤

from-is-cont-bind : ∀ {A : Set} {B} (f : Read A) (g : A → Read B) cs → 
    is-cont ((f >>= g) cs) → 
    ∃ λ x → ∃ λ cs' → (f cs ≡ cont x cs') ∧ (is-cont (g x cs'))
from-is-cont-bind f g cs with f cs 
... | stop _ = ⊥-elim
... | cont x cs' = λ h0 → (x , cs' , refl , h0)

from-is-cont-trunc-bind : ∀ {A : Set} {B} (f : Read A) (g : A → Read B) cs0 cs1 → 
    is-cont ((trunc-bind f g) cs0 cs1) → 
    ∃ λ x → ∃ λ cs → (f cs0 ≡ cont x cs) ∧ (is-cont (g x cs1))
from-is-cont-trunc-bind f g cs0 cs1 with f cs0
... | stop _ = ⊥-elim
... | cont x cs = λ h0 → (x , cs , refl , h0)

elim-is-cont-bind' : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 → 
  is-cont ((f >>= g) cs0) → (∀ a cs1 → (f cs0 ≡ cont a cs1) → (is-cont (g a cs1)) → C) → C
elim-is-cont-bind' f g cs h0 h1 = 
  ex-elim-2 (from-is-cont-bind f g cs h0) λ a cs' (h2 , h3) → h1 a cs' h2 h3

elim-is-cont-bind : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 → 
  (∀ a cs1 → (f cs0 ≡ cont a cs1) → (is-cont (g a cs1)) → C) → is-cont ((f >>= g) cs0) → C 
elim-is-cont-bind f g cs h0 h1 = elim-is-cont-bind' f g cs h1 h0 
    
elim-is-cont-trunc-bind : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 cs1 → 
  (∀ a cs → (f cs0 ≡ cont a cs) → (is-cont (g a cs1)) → C) → 
  is-cont ((trunc-bind f g) cs0 cs1) → C 
elim-is-cont-trunc-bind f g cs0 cs1 h0 h1 = 
  ex-elim-2 (from-is-cont-trunc-bind f g cs0 cs1 h1) 
    λ a cs (h2 , h3) → h0 a cs h2 h3 
    
ends : ∀ {A : Set} → Read A → Set
ends r = ∃ λ cs → is-cont (r cs)

ends-num : ∀ {A : Set} → (Nat → Read A) → Set
ends-num r = ∃ λ k → ends (r k)

passes : ∀ {A : Set} → Read A → A → Set
passes r a = ∃ λ cs0 → ∃ λ cs1 → (r cs0) ≡ cont a cs1

passes-num : ∀ {A : Set} → (Nat → Read A) → A → Set
passes-num r a = ∃ λ k → passes (r k) a

use-seq-eq-just : ∀ {A B C : Set} (r : Read A) (s : Read B) cs0 csf b → 
  ((r >> s) cs0) ≡ cont b csf → 
  (∀ a cs1 → r cs0 ≡ cont a cs1 → (s cs1 ≡ cont b csf) → C) → C
use-seq-eq-just r s cs0 csf b h0 h1 with (r cs0)
... | cont a cs1 = h1 a cs1 refl h0

use-is-cont-seq : ∀ {A B C : Set} (r : Read A) (s : Read B) (cs) → 
  is-cont ((r >> s) cs) → (∀ a cs' → r cs ≡ cont a cs' → (is-cont (s cs')) → C) → C
use-is-cont-seq r s cs h0 h1 with (r cs) 
... | cont a cs' = h1 a cs' refl h0 

use-is-cont-seq' : ∀ {A B C : Set} (r : Read A) (s : Read B) (cs) → 
  (∀ a cs' → r cs ≡ cont a cs' → (is-cont (s cs')) → C) → 
  is-cont ((r >> s) cs) → C
use-is-cont-seq' r s cs h0 h1 = use-is-cont-seq r s cs h1 h0 

elim-ends-seq : ∀ {A B C : Set} (r : Read A) (s : Read B) → 
  (ends r → ends s → C) → ends (r >> s) → C
elim-ends-seq r s h0 = ex-elim' λ cs0 → 
  use-is-cont-seq' r s cs0 λ a cs1 h1 h2 → 
    h0 (cs0 , eq-elim-symm is-cont h1 tt) (cs1 , h2) 

intro-verify : ∀ (Q : Res ⊤ → Set) P B k c cs → 
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
  (∀ msg → Q (stop msg)) → 
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
                  intro-ite {(Read ⊤)} {_} {_} (c ==c 'X') (λ x → (Q (x cs))) hx (h0 _) 
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
  intro-verify (λ x → is-cont x → C) P B k c cs0 
    (elim-is-cont-bind (verify-a B) _ cs0 λ f cs1 h0 h1 → ha f (cs0 , cs1 , h0) (cs1 , h1)) 
    ( elim-is-cont-bind (verify-b B) _ cs0 
        λ (f , g) cs1 h0 h1 → 
          elim-ends-seq (verify P (f ∷ B) k) (verify P (g ∷ B) k) 
            (λ h2 h3 → hb f g (cs0 , cs1 , h0) h2 h3) (cs1 , h1) ) 
    ( elim-is-cont-bind (verify-c B k) _ cs0 
        λ f cs1 h0 h1 → hc f (k , cs0 , cs1 , h0) (cs1 , h1) ) 
    ( elim-is-cont-bind (verify-d B) _ cs0 
        λ f cs1 h0 h1 → hd f (cs0 , cs1 , h0) (cs1 , h1) ) 
    ( elim-is-cont-bind (verify-n B) _ cs0 
        λ f cs1 h0 h1 → hn f (cs0 , cs1 , h0) (cs1 , h1) ) 
    ( elim-is-cont-bind (verify-p P B) _ cs0 
        λ f cs1 h0 h1 → hp f (cs0 , cs1 , h0) (cs1 , h1) ) 
    ( elim-is-cont-bind (verify-s B k) _ cs0 
        λ f cs1 h0 h1 → 
          elim-ends-seq (verify P (not f ∷ B) k) (verify P (f ∷ B) k) 
            (λ h2 h3 → hs f (k , cs0 , cs1 , h0) h2 h3) 
            (cs1 , h1) )
    ( elim-is-cont-bind (verify-t B k) _ cs0 
        λ f cs1 h0 h1 → ht f (k , cs0 , cs1 , h0) (cs1 , h1) ) 
    (λ h0 → hx (cs0 , h0)) 
    (λ _ → ⊥-elim) 
    hv

from-eq-just : ∀ {A : Set} {B} (f : Read A) (g : A → Read B) {cs0} {cs1} {b} → 
   ((f >>= g) cs0) ≡ cont b cs1 → 
   ∃ \ a → ∃ \ cs → (f cs0 ≡ cont a cs) ∧ (g a cs ≡ cont b cs1)
from-eq-just f g {cs0} h with f cs0
... | (cont a cs) = a , cs , refl , h

elim-bind-eq-just : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 cs1 b → 
  (∀ a cs → (f cs0 ≡ cont a cs) → (g a cs ≡ cont b cs1) → C) → 
  ((f >>= g) cs0) ≡ cont b cs1 → C
elim-bind-eq-just f g cs0 csf b h0 h1 with (f cs0)
... | cont a cs1 = h0 a cs1 refl h1

use-bind-eq-just : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 cs1 b → 
  ((f >>= g) cs0) ≡ cont b cs1 → 
  (∀ a cs → (f cs0 ≡ cont a cs) → (g a cs ≡ cont b cs1) → C) → C
use-bind-eq-just f g cs0 cs1 b h0 h1 = ex-elim (from-eq-just f g h0) 
  \ a h2 → ex-elim h2 (λ cs h3 → h1 a cs (fst h3) (snd h3))

elim-obind-eq-just : ∀ {A B C : Set} (f : Maybe A) (g : A → Maybe B) (b : B) → 
  (∀ a → f ≡ just a → (g a) ≡ just b → C) → (f o>= g) ≡ just b → C
elim-obind-eq-just (just a) g b h0 h1 = h0 a refl h1 -- h0 a b refl h1 

use-obind-eq-just : ∀ {A B C : Set} (f : Maybe A) (g : A → Maybe B) (b : B) → 
  (f o>= g) ≡ just b → (∀ a → f ≡ just a → g a ≡ just b → C) → C 
use-obind-eq-just (just a) g b h0 h1 = h1 a refl h0

from-obind-eq-just : ∀ {A B : Set} (f : Maybe A) (g : A → Maybe B) (b : B) → 
  (f o>= g) ≡ just b → ∃ \ a → ((f ≡ just a) ∧ (g a ≡ just b))
from-obind-eq-just nothing _ _  () 
from-obind-eq-just (just a) g b h0 = (a , (refl , h0))

from-lift-read-eq-just : ∀ {A : Set} {f : Maybe A} {a cs0 cs1} → 
  ((lift-read f) cs0 ≡ cont a cs1) → f ≡ just a
from-lift-read-eq-just {_} {just a0} {_} {_} {_} h0 = 
  cong just (cont-inj-val h0) 

from-nth-eq-just : ∀ {A : Set} k l (x : A) → nth k l ≡ just x → x ∈ l
from-nth-eq-just 0 (y ∷ _) x = \ h0 → or-lft (eq-symm (just-inj h0))
from-nth-eq-just (suc m) (_ ∷ ys) x = \ h0 → or-rgt (from-nth-eq-just m ys x h0)

from-get-bch-eq-just : ∀ {B} {m} {f} → get-bch B m ≡ just f → f ∈ B
from-get-bch-eq-just {B} {m} {f} h0 =  
  ex-elim 
    (from-obind-eq-just 
      (rev-index (length B) m) 
      (\ n → nth n B) f h0) 
      \ k h1 → from-nth-eq-just k _ _ (snd h1)

correct-aux : ∀ {f g : Read ⊤} P B c0 c1 cs
  (h0 : is-cont (f cs) → unsat P B)  
  (h1 : is-cont (g cs) → unsat P B)  
  → -------------------------------
  is-cont ((if c0 =c c1 then f else g) cs) → unsat P B 
correct-aux P B c0 c1 cs = 
  intro-ite (c0 =c c1) (λ (x : Read ⊤) → is-cont (x cs) → unsat P B) 

from-lift-read-bind-eq : ∀ {A : Set} B k (m : Form → Maybe A) cs0 csf (a : A) → 
  lift-read (get-bch B k o>= m) cs0 ≡ cont a csf → 
  ∃ λ f → ((f ∈ B) ∧ (m f ≡ just a))
from-lift-read-bind-eq B k m cs0 csf a h0 =
  ex-elim (from-obind-eq-just (get-bch B k) m a (from-lift-read-eq-just h0)) 
    λ f h1 → (f , from-get-bch-eq-just (fst h1) , snd h1)

from-pass-if-seq-eq-just : ∀ {A : Set} b (r : Read A) cs0 csf a → 
  (pass-if b >> r) cs0 ≡ cont a csf → (tr b ∧ (r cs0 ≡ cont a csf))
from-pass-if-seq-eq-just true r cs0 csf a h0 = tt , h0 

from-passes-verify-a : ∀ B f → passes (verify-a B) f → 
  ∃ λ b → ∃ λ g → ((g ∈ B) ∧ (break-a b g ≡ just f))
from-passes-verify-a B f (cs0 , (cs1 , h0)) =
  use-bind-eq-just read-nat _ cs0 cs1 f h0 λ k cs h1 h2 → 
    use-bind-eq-just read-bool _ cs cs1 f h2 λ b cs' h3 h4 → 
      b , from-lift-read-bind-eq B k _ _ _ f h4

from-verify-a-eq-just : ∀ B cs0 cs1 g → verify-a B cs0 ≡ cont g cs1 → 
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

from-verify-b-eq-just : ∀ B cs0 cs1 gh → verify-b B cs0 ≡ cont gh cs1 → 
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
      t , f , chks-good (suc (length B)) t h4 , h6 , h7 

from-verify-c-eq-just : ∀ B k cs0 csf g → (verify-c B k cs0 ≡ cont g csf) →
  ∃ λ t → ∃ λ f → ((good-term (suc (length B)) t) ∧ ((f ∈ B) ∧ (break-c t f ≡ just g)))
from-verify-c-eq-just B k cs0 csf g h0  = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    use-bind-eq-just (read-term k) _ cs1 csf g h1  λ t cs2 h2 h3 → 
      let (h4 , h5) = from-pass-if-seq-eq-just (chk-good-term (suc (length B)) t) _ cs2 csf g h3 
      in ex-elim (from-lift-read-bind-eq B _ _ cs2 csf g h5) λ f (h6 , h7) → 
      t , f , chks-good (suc (length B)) t h4 , h6 , h7 

from-passes-verify-d : ∀ B g → passes (verify-d B) g → 
  ∃ λ f → (f ∈ B) ∧ (break-d (length B) f ≡ just g)
from-passes-verify-d B g (cs0 , csf , h0) =
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → f , h2 , h3

from-verify-d-eq-just : ∀ B cs0 csf g → (verify-d B cs0 ≡ cont g csf) → 
  ∃ λ f → ((f ∈ B) ∧ (break-d (length B) f ≡ just g))
from-verify-d-eq-just B cs0 csf g h0 = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → f , h2 , h3

from-passes-num-verify-s : ∀ B g → passes-num (verify-s B) g → good-form (suc (length B)) g 
from-passes-num-verify-s B g (k , cs0 , csf , h0) = 
  use-bind-eq-just (read-form k) _ cs0 csf g h0 
    λ f cs1 h1 h2 → 
      let (h3 , h4) = from-pass-if-seq-eq-just (chk-good-form _ f) _ cs1 csf _ h2 in 
      let h5 = from-chks-good-form _ f h3 in 
      eq-elim _ (cont-inj-val h4) h5 

from-pass-eq-lft : ∀ {A : Set} (a0 a1 : A) cs0 cs1 → pass a0 cs0 ≡ cont a1 cs1 → a0 ≡ a1
from-pass-eq-lft a0 a1 cs0 cs1 h0 = cont-inj-val h0 

termoid-eq-to-eq : ∀ {b} (t s : Termoid b) → tr (termoid-eq t s) → t ≡ s
termoid-eq-to-eq nil nil _ = refl
termoid-eq-to-eq (cons t0 ts0) (cons t1 ts1) h0 = 
  let (h1 , h2) = tr-band-to-and (termoid-eq t0 _) _ h0 in 
  cong-2 cons (termoid-eq-to-eq _ _ h1) (termoid-eq-to-eq _ _ h2)
termoid-eq-to-eq (var k) (var m) h0 = cong var (nat-eq-to-eq h0)
termoid-eq-to-eq (fun f0 ts0) (fun f1 ts1) h0 = 
  let (h1 , h2) = tr-band-to-and (ftr-eq f0 _) _ h0 in 
  cong-2 fun (ftr-eq-to-eq _ _ h1) (termoid-eq-to-eq _ _ h2)

terms-eq-to-eq : ∀ (t s : Terms) → tr (terms-eq t s) → t ≡ s
terms-eq-to-eq = termoid-eq-to-eq {true}

bct-eq-to-eq : ∀ {b0 b1} → tr (bct-eq b0 b1) → (b0 ≡ b1)
bct-eq-to-eq {or} {or} _ = refl
bct-eq-to-eq {and} {and} _ = refl
bct-eq-to-eq {imp} {imp} _ = refl
bct-eq-to-eq {iff} {iff} _ = refl

form-eq-to-eq : ∀ f g → tr (form-eq f g) → f ≡ g
form-eq-to-eq (cst b0) (cst b1) h0 = cong cst (biff-to-eq h0)
form-eq-to-eq (not f0) (not f1) h0 = cong not (form-eq-to-eq _ _ h0)
form-eq-to-eq (bct b0 f0 g0) (bct b1 f1 g1) h0 = 
  let (h1 , h2 , h3) = tr-band-to-and-3 _ _ _ h0 in
  cong-3 bct (bct-eq-to-eq h1) (form-eq-to-eq f0 f1 h2) (form-eq-to-eq _ _ h3)
form-eq-to-eq (qtf b0 f0) (qtf b1 f1) h0 = 
  let (h1 , h2) = tr-band-to-and _ _ h0 in
  cong-2 qtf (biff-to-eq h1) (form-eq-to-eq _ _ h2)
form-eq-to-eq (rel r0 ts0) (rel r1 ts1) h0 = 
  let (h1 , h2) = tr-band-to-and _ _ h0 in
  cong-2 rel (ftr-eq-to-eq _ _ h1) (termoid-eq-to-eq _ _ h2)

from-chks-mono-fun : ∀ k m f → tr (chk-mono-fun k m f) → mono-fun k m f
from-chks-mono-fun k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) h0 = 
  let h1 = from-chks-mono-fun k (suc m) f (from-tr-bsnd (c =c '=') _ h0) in 
  let h2 = char-eq-to-eq _ _ (from-tr-bfst (c =c '=') _ h0) in 
  eq-elim 
    ( λ x →
        mono-fun k m
          (∀* (∀* (rel (sf (x ∷ [])) (cons (var 1) (cons (var zero) nil)) →* f))) )
    (eq-symm h2) (mono-fun-fa k m f h1) 
from-chks-mono-fun k m (rel (sf (c ∷ [])) (cons (fun f0 ts0) (cons (fun f1 ts1) nil))) ht0 = 
  let (h1 , h2 , h3 , h4 , h5) = tr-band-to-and-5 (c =c '=') _ _ _ _ ht0 in 
  eq-elim-4 (λ x y z w → mono-fun k m (rel (sf (x ∷ [])) (cons (fun f0 y) (cons (fun z w) nil))))
    (eq-symm (char-eq-to-eq _ _ h1)) 
    (eq-symm (termoid-eq-to-eq _ _ h4)) 
    (ftr-eq-to-eq f0 f1 h3) 
    (eq-symm (termoid-eq-to-eq _ _ h5)) 
    (mono-fun-eq k m f0 (from-chks-good-ftr (suc k) f0 h2))

from-chks-mono-rel : ∀ k m f → tr (chk-mono-rel k m f) → mono-rel k m f
from-chks-mono-rel k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) h0 = 
  let h1 = from-chks-mono-rel k (suc m) f (from-tr-bsnd (c =c '=') _ h0) in 
  let h2 = char-eq-to-eq _ _ (from-tr-bfst (c =c '=') _ h0) in 
  eq-elim 
    ( λ x →
        mono-rel k m
          (∀* (∀* (rel (sf (x ∷ [])) (cons (var 1) (cons (var zero) nil)) →* f))) )
    (eq-symm h2) (mono-rel-fa k m f h1) 
from-chks-mono-rel k m (bct imp (rel r0 ts0) (rel r1 ts1)) ht0 =  
  let (h1 , h2 , h3 , h4) = tr-band-to-and-4 (chk-good-ftr (suc k) r0) _ _ _ ht0 in 
  eq-elim-3 (λ x y z → mono-rel k m (rel r0 y →* rel x z)) 
    (ftr-eq-to-eq r0 _ h2) 
    (eq-symm (termoid-eq-to-eq _ _ h3)) 
    (eq-symm (termoid-eq-to-eq _ _ h4)) 
    (mono-rel-imp k m r0 (from-chks-good-ftr (suc k) r0 h1))

from-chks-vars-lt-termoid : ∀ {b} k (t : Termoid b) → tr (chk-vars-lt-termoid k t) → vars-lt-termoid k t
from-chks-vars-lt-termoid k nil h0 = tt
from-chks-vars-lt-termoid k (cons t ts) h0 = 
  let (h1 , h2) = tr-band-to-and _ _ h0 in 
  from-chks-vars-lt-termoid k t h1 , from-chks-vars-lt-termoid k ts h2
from-chks-vars-lt-termoid k (var m) h0 = nat-lt-to-lt _ _ h0
from-chks-vars-lt-termoid k (fun _ ts) h0 = from-chks-vars-lt-termoid k ts h0

from-chks-vars-lt-form : ∀ k f → tr (chk-vars-lt-form k f) → vars-lt-form k f
from-chks-vars-lt-form k (cst b) _ = tt
from-chks-vars-lt-form k (not f) h0 = from-chks-vars-lt-form k f h0
from-chks-vars-lt-form k (bct b f g) h0 = 
  let (h1 , h2) = tr-band-to-and _ _ h0 in 
  from-chks-vars-lt-form k f h1 , from-chks-vars-lt-form k g h2 
from-chks-vars-lt-form k (qtf _ f) h0 = from-chks-vars-lt-form (suc k) f h0
from-chks-vars-lt-form k (rel _ ts) h0 = from-chks-vars-lt-termoid k ts h0

from-chks-choice : ∀ k m f → tr (chk-choice k m f) → choice k m f
from-chks-choice k m (qtf false f) h0 = choice-fa k m _ (from-chks-choice k (suc m) f h0)
from-chks-choice k m (bct imp (qtf true f) g) ht0 = 
  let (h1 , h2 , h3) = tr-band-to-and-3 (chk-good-form k f) _ _ ht0 in 
  let h4 = from-chks-good-form k f h1 in 
  let hlt = from-chks-vars-lt-form (suc m) f h2 in 
  elim-bor (form-eq (subst-form 0 _ f) g) _ 
    ( λ h5 → 
        let h6 = form-eq-to-eq (subst-form _ _ f) _ h5 in 
        eq-elim (λ x → choice k m ((∃* f) →* x)) h6 
          (choice-imp-asc k m f h4 hlt) ) 
    ( λ h5 → 
        let h6 = form-eq-to-eq (subst-form _ _ f) _ h5 in 
        eq-elim (λ x → choice k m ((∃* f) →* x)) h6 
          (choice-imp-desc k m f h4 hlt) ) 
   h3

from-chks-pred-def : ∀ k m f → tr (chk-pred-def k m f) → pred-def k m f
from-chks-pred-def k m (qtf false f) h0 = pred-def-fa k m _ (from-chks-pred-def k (suc m) f h0)
from-chks-pred-def k m (bct iff (rel (nf n) ts) f) h0 = 
  let (h1 , h2 , h3 , h4) = tr-band-to-and-4 (k =n n) (chk-good-form k f) (chk-vars-lt-form m f) _ h0 in 
  let h5 = nat-eq-to-eq {k} h1 in 
  let h6 = from-chks-good-form k f h2 in 
  let h7 = from-chks-vars-lt-form m f h3 in 
  elim-bor (terms-eq ts _) _ 
    ( λ h8 → 
        let h9 = eq-symm (terms-eq-to-eq ts _ h8) in 
        eq-elim-2 (λ x y → pred-def k m (rel (nf x) y ↔* f)) h5 h9 
          (pred-def-iff-asc k m f h6 h7) ) 
    ( λ h8 → 
        let h9 = eq-symm (terms-eq-to-eq ts _ h8) in 
        eq-elim-2 (λ x y → pred-def k m (rel (nf x) y ↔* f)) h5 h9 
          (pred-def-iff-desc k m f h6 h7) ) 
    h4

from-chks-jst : ∀ k f → tr (chk-jst k f) → jst k f
from-chks-jst k f = elim-bor (form-eq f (cst true)) _ 
  ( λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (cst true) h0) (jst-top _)) 
    (elim-bor (form-eq f (not (cst false))) _ 
    (λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (not (cst false)) h0) (jst-not-bot _)) 
    (elim-bor (form-eq f _) _ 
      ((λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (refl-axiom) h0) (jst-refl _))) 
      (elim-bor (form-eq f symm-axiom) _ (λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (symm-axiom) h0) (jst-symm _)) 
        (elim-bor (form-eq f trans-axiom) _
 (λ h0 →
    eq-elim-symm (jst k) (form-eq-to-eq f trans-axiom h0) (jst-trans _))
   (elim-bor (chk-mono-rel k 0 f) _ (λ h0 → jst-rel k f (from-chks-mono-rel k 0 f h0)) 
     (elim-bor (chk-mono-fun k 0 f) _ (λ h0 → jst-fun k f (from-chks-mono-fun k 0 f h0)) 
       (elim-bor (chk-choice k 0 f) _ 
         ((λ h0 → jst-choice k f (from-chks-choice k 0 f h0))) 
         (λ h0 → jst-pred-def k f (from-chks-pred-def k 0 f h0))))))))) 

from-passes-num-verify-t : ∀ B g → passes-num (verify-t B) g → jst (length B) g 
from-passes-num-verify-t B g (k , cs0 , csf , h0) = 
  use-bind-eq-just (read-form k) _ cs0 csf g h0 (λ f cs1 h1 h2 → 
    let (h3 , h4) = from-pass-if-seq-eq-just (chk-jst (length B) f) _ cs1 csf _ h2 in 
    let h5 = from-pass-eq-lft f g cs1 csf h4 in
    let h6 = from-chks-jst (length B) f h3 in 
    eq-elim (jst (length B)) h5 h6)

elim-ends-bind : ∀ {A B C : Set} (f : Read A) (g : A → Read B) → 
  (∀ a → passes f a → ends (g a) → C) → ends (f >>= g) → C
elim-ends-bind f g h0 (cs0 , h1) = 
  elim-is-cont-bind f g cs0 
    (λ a cs1 h2 h3 → h0 a (cs0 , cs1 , h2) (cs1 , h3)) 
    h1

elim-ends-lift-read-get-bch : ∀ {A C : Set} B k (r : Form → Read A) → 
  (∀ f → (f ∈ B) → ends (r f) → C) → ends (lift-read (get-bch B k) >>= r) → C
elim-ends-lift-read-get-bch B k r h0 = 
  elim-ends-bind (lift-read (get-bch B k)) r 
    λ f (cs0 , cs1 , h1) → 
    h0 f (from-get-bch-eq-just (from-lift-read-eq-just {_} {get-bch B k} h1))

from-ends-pass-if : ∀ b → ends (pass-if b) → tr b
from-ends-pass-if true _ = tt

from-ends-verify-x : ∀ B → ends (verify-x B) → ∃ λ f → (f ∈ B) ∧ ((not f) ∈ B)
from-ends-verify-x B = 
  elim-ends-bind read-nat _ 
    λ k h0 → 
      elim-ends-bind read-nat _ 
        λ m h1 → 
          elim-ends-lift-read-get-bch B k _ 
            λ f h2 → 
              elim-ends-lift-read-get-bch B m _ 
                λ g h3 h4 → 
                  let h5 = form-eq-to-eq f (not g) (from-ends-pass-if (form-eq f (not g)) h4) in 
                  g , h3 , eq-elim (λ x → x ∈ B) h5 h2 

in-prob-cons : ∀ f P p → in-prob f P → in-prob f (p ∷ P) 
in-prob-cons f P p = ex-elim' λ nm h0 → (nm , or-rgt h0)

from-get-from-prob-eq : ∀ P nm0 cs0 cs1 f → 
  get-from-prob P nm0 cs0 ≡ cont f cs1 → (in-prob f P) 
from-get-from-prob-eq ((nm1 , g) ∷ P) nm0 cs0 cs1 f = 
  intro-ite {_} {pass g} (chars-eq nm1 nm0)
    (λ x → x cs0 ≡ cont f cs1 → in-prob f ((nm1 , g) ∷ P)) 
    ( λ h0 → eq-elim (λ x → in-prob x ((nm1 , g) ∷ P)) 
      (cont-inj-val h0) 
      (nm1 , or-lft refl) ) 
    λ h0 → in-prob-cons _ _ _ (from-get-from-prob-eq P nm0 cs0 cs1 f h0)

from-passes-verify-p : ∀ P B g → passes (verify-p P B) g → 
  in-prob g P ∧ good-form (suc (length B)) g
from-passes-verify-p P B g (cs0 , csf , h0) =
  use-bind-eq-just read-chars _ cs0 csf g h0 λ nm cs1 h1 h2 → 
    use-bind-eq-just (get-from-prob P nm) _ cs1 csf g h2 λ f cs2 h3 h4 → 
    let h5 = from-get-from-prob-eq P _ _ _ _ h3 in 
    let (h6 , h7) = from-pass-if-seq-eq-just (chk-good-form (suc (length B)) f) _ cs2 csf g h4 in 
    let h8 = from-pass-eq-lft _ _ _ _ h7 in 
    eq-elim (λ x → in-prob x P ∧ good-form (suc (length B)) x) h8 (h5 , from-chks-good-form _ f h6)

from-verify-p-eq-just : ∀ P B cs0 csf g → (verify-p P B cs0 ≡ cont g csf) → 
  (in-prob g P ∧ good-form (suc (length B)) g)
from-verify-p-eq-just P B cs0 csf g h0 = 
  use-bind-eq-just read-chars _ cs0 csf g h0 λ nm cs1 h1 h2 → 
    use-bind-eq-just (get-from-prob P nm) _ cs1 csf g h2 λ f cs2 h3 h4 → 
    let h5 = from-get-from-prob-eq P _ _ _ _ h3 in 
    let (h6 , h7) = from-pass-if-seq-eq-just (chk-good-form (suc (length B)) f) _ cs2 csf g h4 in 
    let h8 = from-pass-eq-lft _ _ _ _ h7 in 
    eq-elim (λ x → in-prob x P ∧ good-form (suc (length B)) x) h8 (h5 , from-chks-good-form _ f h6)

from-passes-verify-n : ∀ B g → passes (verify-n B) g → (not (not g)) ∈ B
from-passes-verify-n B g (cs0 , csf , h0) = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → 
     eq-elim (λ x → x ∈ B) (from-break-n-eq-just f g h3) h2

from-verify-n-eq-just : ∀ B cs0 csf g → (verify-n B cs0 ≡ cont g csf) → (not (not g)) ∈ B
from-verify-n-eq-just B cs0 csf g h0 = 
  use-bind-eq-just read-nat _ cs0 csf g h0 λ m cs1 _ h1 → 
    ex-elim (from-lift-read-bind-eq B _ _ cs1 csf g h1) λ f (h2 , h3) → 
      eq-elim (λ x → x ∈ B) (from-break-n-eq-just f g h3) h2
    
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
      prsv-t P B g hP hB h2 (correct-core P _ k hP (good-bch-t B g h2 hB) h1) ) 
  ( λ h0 R F V hR → 
      ex-elim (from-ends-verify-x B h0) 
        λ g (h1 , h2) → 
          elim-lem (R , F , V ⊨ g) 
            (λ h3 → not g , or-rgt h2 , dni h3) 
            λ h3 → g , or-rgt h1 , h3 )

correct-init : ∀ P k → good-prob P → ends (verify P [] k) → unsat-prob P
correct-init P k hP hp R F V hR =
  ex-elim (correct-core P [] k hP pall-nil hp R F V hR) 
    (λ f (h0 , h1) → f , or-elim h0 (λ h2 → h2 , h1) ⊥-elim)

nothing-ne-just : ∀ {A} (a : A) → nothing ≠ just a
nothing-ne-just _ ()

elim-seq-eq-just : ∀ {A B C : Set} (f : Read A) (g : Read B) cs0 csf b → 
  (∀ a cs1 → f cs0 ≡ cont a cs1 → g cs1 ≡ cont b csf → C) → 
  ((f >> g) cs0 ≡ cont b csf) → C
elim-seq-eq-just f g cs0 csf b h0 h1 with (f cs0)
... | cont a' cs1' = h0 a' cs1' refl h1 

elim-alt-eq-just : ∀ {A C : Set} (f : Read A) (g : Read A) cs0 cs1 a → 
  (f cs0 ≡ cont a cs1 → C) → (g cs0 ≡ cont a cs1 → C) → 
  ((f <|> g) cs0 ≡ cont a cs1) → C
elim-alt-eq-just f g cs0 cs1 a h0 h1 with (f cs0)
... | cont a' cs1' = h0 
... | stop _ = h1 

elim-passes-alt : ∀ {A C : Set} (f : Read A) (g : Read A) (a : A) → 
  (passes f a → C) → (passes g a → C) → passes (f <|> g) a → C
elim-passes-alt f g a h0 h1 (cs0 , csf , h2) = 
  elim-alt-eq-just f g cs0 csf a 
    (λ h2 → h0 (cs0 , csf , h2)) 
    (λ h2 → h1 (cs0 , csf , h2)) 
    h2 

elim-eq-symm : ∀ {A : Set} {x : A} {y : A} (p : A → Set) → p y → x ≡ y → p x 
elim-eq-symm p h0 refl = h0

elim-passes-seq : ∀ {A B C : Set} (f : Read A) (g : Read B) (b : B) → 
  (ends f → passes g b → C) → passes (f >> g) b → C
elim-passes-seq f g b h0 (cs0 , csf , h1) = 
  elim-seq-eq-just f g cs0 csf b 
    ( λ a cs1 h2 h3 → h0 (cs0 , eq-elim-symm is-cont h2 tt) (cs1 , csf , h3) ) 
    h1

elim-passes-bind : ∀ {A B C : Set} (f : Read A) (g : A → Read B) (b : B) → 
  (∀ a → passes f a → passes (g a) b → C) → passes (f >>= g) b → C
elim-passes-bind f g b h0 (cs0 , csf , h1) = 
  elim-bind-eq-just f g cs0 csf b 
    ( λ a cs1 h2 h3 → h0 a (cs0 , cs1 , h2) (cs1 , csf , h3)) h1

elim-pass-eq-just : ∀ {A B : Set} (a0 a1 : A) cs0 cs1 → 
  (a0 ≡ a1 → cs0 ≡ cs1 → B) → 
  pass a0 cs0 ≡ cont a1 cs1 → B
elim-pass-eq-just a0 a1 cs0 cs1 h0 refl = h0 refl refl

elim-in-prob-cons : ∀ {C} f i g P → (f ≡ g → C) → (in-prob f P → C) → in-prob f ((i , g) ∷ P) → C
elim-in-prob-cons f i g P h0 h2 (j , h3) = 
  or-elim' (λ h4 → h0 (prod-inj-rgt h4)) (λ h4 → h2 (j , h4)) h3

good-prob-cons : ∀ n f P → (∀ k → good-form k f) → good-prob P → good-prob ((n , f) ∷ P)
good-prob-cons n f P h0 h1 g m = 
  elim-in-prob-cons _ _ _ _ 
    (λ h2 → elim-eq (good-form m) (h0 _) (eq-symm h2)) (h1 _ _)

elim-passes-fail : ∀ {A B : Set} (a : A) st → passes (fail st) a → B
elim-passes-fail _ _ (_ , _ , ()) 

elim-passes-pass : ∀ {A B : Set} (a0 a1 : A) → 
  (a0 ≡ a1 → B) → passes (pass a0) a1 → B
elim-passes-pass a0 a1 h0 (cs0 , csf , h1) = h0 (cont-inj-val h1) 

from-good-form-zero : ∀ k f → good-form 0 f → good-form k f
from-good-form-zero 0 f = id
from-good-form-zero (suc k) f h0 = 
  good-form-suc k f (from-good-form-zero k f h0)

read-prob-core-good-prob : ∀ (P : Prob) k → passes (read-prob-core k) P → good-prob P
read-prob-core-good-prob P (suc k) = 
  elim-passes-alt (read-spec-char _ >> pass []) _ P 
    ( elim-passes-seq (read-spec-char _) (pass []) P 
        λ _ → elim-passes-pass [] P (elim-eq good-prob good-prob-nil) ) 
    ( elim-passes-seq (read-spec-char _) _ P 
        λ _ → 
          elim-passes-bind (read-af k) _ P 
            λ (i , f) h0 → 
              elim-passes-seq (pass-if (chk-good-form 0 f)) _ P 
                λ h1 → elim-passes-bind (read-prob-core k) _ P 
                  λ Q h2 → elim-passes-pass _ _ 
                    ( elim-eq good-prob 
                        ( good-prob-cons i f Q 
                            ( λ m → from-good-form-zero m f 
                                (from-chks-good-form 0 f (from-ends-pass-if _ h1)) ) 
                            (read-prob-core-good-prob Q k h2) ) ) ) 

correct : ∀ (cs-prob cs-prf : Chars) → is-cont (check cs-prob cs-prf) →
  ∃ λ (P : Prob) → ∃ λ (cs : Chars) → (read-prob cs-prob ≡ cont P cs) ∧ (unsat-prob P) 
correct cs0 cs1 = 
  elim-is-cont-trunc-bind read-prob _ cs0 cs1 
    λ P cs h0 h1 → P , cs , h0 , 
      correct-init P (length cs1) (read-prob-core-good-prob P (length cs0) (cs0 , cs , h0)) 
        (cs1 , h1) 