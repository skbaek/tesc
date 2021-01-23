module correct (D : Set) (wit : D) where

open import Data.Empty
open import Relation.Nullary
open import Data.Unit.Base 
open import Data.Bool
  hiding (not)
  renaming (_<_ to _<b_)
  renaming (_∧_ to _&&_)
  renaming (_∨_ to _||_)
open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
  renaming (_==_ to _=n_)
open import Data.Nat.Base 
  using (_<_)
  using (z≤n)
  using (s≤s)
open import Data.Nat.Properties 
  using (<-trans)
  using (<-cmp)
  using (<-irrefl)
  using (<ᵇ⇒<)
  using (≡⇒≡ᵇ)
  using (≡ᵇ⇒≡)
open import Data.Char
  renaming (_==_ to _=c_)
  renaming (_<_ to _<c_)
open import Agda.Builtin.Equality
open import Data.List 
  renaming (or to disj) 
  renaming(and to conj)
open import Data.Maybe
  renaming (_>>=_ to _o>=_)
open import Relation.Binary.Definitions 
  using (tri<)
  using (tri≈)
  using (tri>)
open import Data.Product
open import basic 
  hiding (F)
open import verify 



-------- Semantics --------

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
R , F , V ⊨ (cst b) = T b 
R , F , V ⊨ (not f) = ¬ (R , F , V ⊨ f)
R , F , V ⊨ (bct or f g) = (R , F , V ⊨ f) ∨ (R , F , V ⊨ g)
R , F , V ⊨ (bct and f g) = (R , F , V ⊨ f) ∧ (R , F , V ⊨ g)
R , F , V ⊨ (bct imp f g) = (R , F , V ⊨ f) → (R , F , V ⊨ g)
R , F , V ⊨ (bct iff f g) = (R , F , V ⊨ f) ↔ (R , F , V ⊨ g)
R , F , V ⊨ (qtf false f) = ∀ (x) → (R , F , (V / 0 ↦ x) ⊨ f)
R , F , V ⊨ (qtf true f) = ∃ (λ x → (R , F , (V / 0 ↦ x) ⊨ f))
R , F , V ⊨ (rel r ts) = T (R r (terms-val F V ts))

standard : RA → Set 
standard R = ∀ d0 d1 → (T (R (sf [ '=' ]) (d0 ∷ d1 ∷ [])) ↔ (d0 ≡ d1))

sats : RA → FA → VA → Bch → Set
sats R F V B = ∀ f → mem f B → R , F , V ⊨ f

sat : Bch → Set
sat B = ∃ λ R → ∃ λ F → ∃ λ V → (standard R ∧ sats R F V B)

unsat : Bch → Set
unsat B = ¬ (sat B)

_=>_ : Form → Form → Set 
f => g = ∀ R F V → (R , F , V ⊨ bct imp f g)



-------- nth --------

mem-nth : ∀ B k → mem (nth k B) B ∨ (nth k B ≡ ⊤*)
mem-nth B k = or-elim (mem-lookup B k ⊤*) or-lft or-rgt

sats-nth : ∀ R F V B k → sats R F V B → R , F , V ⊨ nth k B
sats-nth R F V B k h0 = or-elim (mem-nth B k) (h0 _) 
  (elim-eq-symm (λ x → R , F , V ⊨ x) tt)



-------- Good --------

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
good-bch B = ∀ f → mem f B → good-form (size B) f

best-bch : Bch → Set
best-bch B = ∀ f k → mem f B → good-form k f

good-ftr-suc : ∀ k f → good-ftr k f → good-ftr (suc k) f
good-ftr-suc k (nf m) h = <-trans h (n<sn _) 
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

good-bch-add : ∀ B f → good-bch B → good-form (suc (size B)) f → good-bch (add B f)
good-bch-add B f hB hf = 
  let heq = size-add B f in 
  all-add (good-form (size (add B f))) B f 
    (λ g hg → elim-eq-symm (λ x → good-form x g) (good-form-suc (size B) g (hB g hg)) heq)
    (elim-eq-symm (λ x → good-form x f) hf heq)
    
good-form-nth : ∀ B k → good-bch B → good-form (size B) (nth k B)
good-form-nth B k h = or-elim (mem-nth B k) (h _) 
  λ h1 → eq-elim-symm (good-form (size B)) h1 tt

good-subst-termoid : ∀ {b} s (t : Termoid b) k m → good-term k s → 
  good-termoid k t → good-termoid k (subst-termoid m s t)
good-subst-termoid {true} _ nil _ _ _ _ = tt
good-subst-termoid {true} s (cons t ts) k m h0 h1 = 
  (good-subst-termoid s _ _ _ h0 (fst h1)) ,
  (good-subst-termoid s _ _ _ h0 (snd h1)) 
good-subst-termoid {false} s (var n) k m h0 h1 = 
  tri-intro-lem m n (good-termoid k) (\ _ → tt) (\ _ → h0) (\ _ → tt)
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
prsv-good-a-core : ∀ k f → good-form k f → 
  (good-form k (apply-a false f) ∧ good-form k (apply-a true f))

good-term-par : ∀ k → good-term (suc k) (par k)
good-term-par k = n<sn _ , tt

prsv-good-a-core _ (cst _) _ = tt , tt 
prsv-good-a-core k (bct and f g) = id
prsv-good-a-core k (bct iff f g) (hf , hg) = (hf , hg) , (hg , hf) 
prsv-good-a-core _ (bct or _ _) _ = tt , tt 
prsv-good-a-core _ (bct imp _ _) _ = tt , tt 
prsv-good-a-core _ (qtf _ _) _ = tt , tt 
prsv-good-a-core _ (rel _ _) _ = tt , tt 
prsv-good-a-core k (not (cst _)) _ =  tt , tt
prsv-good-a-core k (not (bct or f g)) = id 
prsv-good-a-core _ (not (bct and _ _)) _ = tt , tt 
prsv-good-a-core k (not (bct imp f g)) = id
prsv-good-a-core _ (not (bct iff _ _)) _ = tt , tt 
prsv-good-a-core _ (not (qtf _ _)) _ = tt , tt 
prsv-good-a-core _ (not (not _)) _ = tt , tt 
prsv-good-a-core _ (not (rel _ _)) _ = tt , tt 

prsv-good-a : ∀ k b f → good-form k f → good-form k (apply-a b f)
prsv-good-a k false f h0 = fst (prsv-good-a-core k f h0)
prsv-good-a k true  f h0 = snd (prsv-good-a-core k f h0)

prsv-good-b : ∀ k f → good-form k f → 
  (good-form k (fst (apply-b f)) ∧ good-form k (snd (apply-b f)))
prsv-good-b _ (cst _) _ = tt , tt 
prsv-good-b k (bct or f g) = id
prsv-good-b k (bct imp f g) = id 
prsv-good-b _ (bct and _ _) _ = tt , tt 
prsv-good-b _ (bct iff _ _) _ = tt , tt 
prsv-good-b _ (qtf _ _) _ = tt , tt 
prsv-good-b _ (rel _ _) _ = tt , tt 
prsv-good-b k (not (cst _)) _ =  tt , tt
prsv-good-b k (not (bct and f g)) = id 
prsv-good-b _ (not (bct or _ _)) _ = tt , tt 
prsv-good-b k (not (bct iff f g)) (hf , hg) = (hf , hg) , (hg , hf) 
prsv-good-b _ (not (bct imp _ _)) _ = tt , tt 
prsv-good-b _ (not (qtf _ _)) _ = tt , tt 
prsv-good-b _ (not (not _)) _ = tt , tt 
prsv-good-b _ (not (rel _ _)) _ = tt , tt 

prsv-good-c : ∀ k t f → good-term k t → good-form k f → good-form k (apply-c t f)
prsv-good-c k t (qtf false f) h0 h1 = good-subst-form t f k 0 h0 h1 
prsv-good-c k t (not (qtf true f)) h0 h1 = good-subst-form t (not f) k 0 h0 h1 
prsv-good-c _ _ (rel _ _) _ _ = tt
prsv-good-c _ _ (bct _ _ _) _ _ = tt
prsv-good-c _ _ (cst _) _ _ = tt
prsv-good-c _ _ (qtf true _) _ _ = tt
prsv-good-c _ _ (not (rel _ _)) _ _ = tt
prsv-good-c _ _ (not (bct _ _ _)) _ _ = tt
prsv-good-c _ _ (not (cst _)) _ _ = tt
prsv-good-c _ _ (not (not _)) _ _ = tt
prsv-good-c k t (not (qtf false _)) _ _ = tt

prsv-good-d : ∀ k f → good-form k f → good-form (suc k) (apply-d k f)
prsv-good-d k (qtf true f) h0 = 
  good-subst-form (par k) f (suc k) 0 (good-term-par k) (good-form-suc k f h0)
prsv-good-d k (not (qtf false f)) h0 = 
  good-subst-form (par k) f (suc k) 0 (good-term-par k) (good-form-suc k f h0)
prsv-good-d k (cst _) h0 = tt
prsv-good-d k (rel _ _) h0 = tt
prsv-good-d k (bct _ _ _) h0 = tt
prsv-good-d k (qtf false _) h0 = tt
prsv-good-d k (not (cst _)) h0 = tt
prsv-good-d k (not (rel _ _)) h0 = tt
prsv-good-d k (not (bct _ _ _)) h0 = tt
prsv-good-d k (not (not  _)) h0 = tt
prsv-good-d k (not (qtf true _)) h0 = tt

prsv-good-n : ∀ k f → good-form k f → good-form k (apply-n f)
prsv-good-n k (not (not f)) = id
prsv-good-n _ (cst _) _ = tt
prsv-good-n _ (rel _ _) _ = tt
prsv-good-n _ (bct _ _ _) _ = tt
prsv-good-n _ (qtf _ _) _ = tt
prsv-good-n _ (not (cst _)) _ = tt
prsv-good-n _ (not (rel _ _)) _ = tt
prsv-good-n _ (not (bct _ _ _)) _ = tt
prsv-good-n _ (not (qtf _ _)) _ = tt

good-bch-a : ∀ B i b → good-bch B → good-bch (add B (apply-a b (nth i B)))
good-bch-a B i b h0  = 
  good-bch-add B _ h0 
    ( good-form-suc _ (apply-a b (nth i B)) 
      (prsv-good-a _ b _ (good-form-nth B i h0)) )

good-bch-b : ∀ B k → good-bch B → 
  (good-bch (add B (fst (apply-b (nth k B)))) ∧ good-bch (add B (snd (apply-b (nth k B)))))
good-bch-b B k h0 = 
  let (h2 , h3) = prsv-good-b (size B) (nth k B) (good-form-nth B k h0) in
  (good-bch-add B _ h0 (good-form-suc (size B) (fst (apply-b (nth k B))) h2)) , 
  (good-bch-add B _ h0 (good-form-suc (size B) (snd (apply-b (nth k B))) h3))

good-bch-c : ∀ B k t → good-bch B → good-term (suc (size B)) t → 
  (good-bch (add B (apply-c t (nth k B))))
good-bch-c B k t h0 h2 = good-bch-add B _ h0  
  (prsv-good-c _ t (nth k B) h2 (good-form-suc _ (nth k B) (good-form-nth B k h0))) 

good-bch-d : ∀ B k → good-bch B → good-bch (add B (apply-d (size B) (nth k B)))
good-bch-d B k h0 = 
  good-bch-add B _ h0 (prsv-good-d (size B) (nth k B) (good-form-nth B k h0))

good-bch-n : ∀ B k → good-bch B → good-bch (add B (apply-n (nth k B)))
good-bch-n B k h0 = 
  good-bch-add B _ h0 
    (prsv-good-n _ (nth k B) (good-form-suc _ (nth k B) (good-form-nth _ _ h0)))  

chks-good-ftr : ∀ k f → T (chk-good-ftr k f) → good-ftr k f
chks-good-ftr k (nf m) h = <ᵇ⇒< _ _ h 
chks-good-ftr _ (sf _) _ = tt

chks-good-termoid : ∀ {b} k (t : Termoid b) → T (chk-good-termoid k t) → good-termoid k t 
chks-good-termoid {true} _ nil _ = tt
chks-good-termoid {true} k (cons t ts) h0 = 
  chks-good-termoid _ _ (bfst _ _ h0) , chks-good-termoid _ _ (bsnd _ _ h0)
chks-good-termoid {false} k (var m) h0 = tt
chks-good-termoid {false} k (fun f ts) h0 =
  chks-good-ftr _ _ (bfst _ _ h0) , 
  chks-good-termoid _ _ (bsnd _ _ h0)

chks-good-form : ∀ k f → T (chk-good-form k f) → good-form k f  
chks-good-form _ (cst _) _ = tt
chks-good-form k (bct _ f g) h0 =  
  (chks-good-form k f (bfst _ _ h0)) , 
  (chks-good-form k g (bsnd _ _ h0))
chks-good-form k (not f) h0 = chks-good-form k f h0
chks-good-form k (qtf _ f) h0 = chks-good-form k f h0
chks-good-form k (rel r ts) h0 = 
  chks-good-ftr _ r (bfst _ _ h0) , 
  chks-good-termoid _ ts (bsnd _ _ h0) 

sats-add : ∀ R F V B f → sats R F V B → (R , F , V ⊨ f) → sats R F V (add B f)
sats-add R F V B f h0 h1 g h2 = or-elim (from-mem-add B g _ h2) (h0 _) (elim-eq-symm _ h1)

prsv-implies : ∀ B k (f : Form → Form) →
  (∀ g → g => f g) → sat B → sat (add B (f (nth k B))) 
prsv-implies B k f h0 h1 = 
  ex-elim-3 h1 
    λ R F V (h2 , h3) → 
      R , F , V , h2 , 
        λ g h4 → 
          or-elim (from-mem-add B g _ h4) (h3 g) 
            (elim-eq-symm (λ x → R , F , V ⊨ x) (h0 (nth k B) R F V (sats-nth R F V B k h3)))
  
implies-top : ∀ f → (f => ⊤*) 
implies-top _ _ _ _ _ = tt

implies-a : ∀ f → ((f => apply-a false f) ∧ (f => apply-a true f))
implies-a f@(cst _) = implies-top f , implies-top f
implies-a (bct and f g) = (λ _ _ _ → fst) , (λ _ _ _ → snd)
implies-a (bct iff f g) = (λ _ _ _ → fst) , (λ _ _ _ → snd)
implies-a f@(bct or _ _) =  implies-top f , implies-top f
implies-a f@(bct imp _ _) = implies-top f , implies-top f
implies-a f@(qtf _ _) = implies-top f , implies-top f
implies-a f@(rel _ _) = implies-top f , implies-top f
implies-a f@(not (cst _)) = implies-top f , implies-top f
implies-a (not (bct or f g)) = (λ _ _ _ → not-or-lft) , (λ _ _ _ → not-or-rgt)
implies-a f@(not (bct and _ _)) = implies-top f , implies-top f
implies-a (not (bct imp f g)) = (λ _ _ _ → not-imp-lft) , (λ _ _ _ → not-imp-rgt)
implies-a f@(not (bct iff _ _)) = implies-top f , implies-top f
implies-a f@(not (qtf _ _)) = implies-top f , implies-top f
implies-a f@(not (not _)) = implies-top f , implies-top f
implies-a f@(not (rel _ _)) = implies-top f , implies-top f

implies-b : ∀ f → f => (fst (apply-b f) ∨* snd (apply-b f)) 
implies-b (cst _) _ _ _ _ = or-lft tt
implies-b (bct or f g) R F V = id
implies-b (bct imp f g) R F V = imp-to-not-or
implies-b (not (bct and f g)) _ _ _ = not-and-to-not-or-not
implies-b (not (bct iff f g)) _ _ _ = not-and-to-not-or-not
implies-b (not (bct or _ _)) _ _ _ _ = or-lft tt
implies-b (not (bct imp _ _)) _ _ _ _ = or-lft tt
implies-b (not (cst _)) _ _ _ _ = or-lft tt
implies-b (not (qtf _ _)) _ _ _ _ = or-lft tt
implies-b (not (not _)) _ _ _ _ = or-lft tt
implies-b (not (rel _ _)) _ _ _ _ = or-lft tt
implies-b (rel _ _) _ _ _ _ = or-lft tt
implies-b (bct and _ _) _ _ _ _ = or-lft tt
implies-b (bct iff _ _) _ _ _ _ = or-lft tt
implies-b (qtf _ _) _ _ _ _ = or-lft tt

termoid-val-subst : ∀ (F : FA) (V : VA) (k : Nat) (b : Bool) (s : Term) (t : Termoid b) → 
  (termoid-val F (V / k ↦ term-val F V s) t) ≡ (termoid-val F V (subst-termoid k s t))
termoid-val-subst F V k true s nil = refl
termoid-val-subst F V k true s (cons t ts) = 
  cong-2 _∷_ (termoid-val-subst F V k false s t) 
    (termoid-val-subst F V k true s ts)
termoid-val-subst F V k false s (var m) = 
  tri-intro-lem k m 
    (λ x → (V / k ↦ term-val F V s) m ≡ termoid-val F V x)
    (λ h0 → eq-trans _ (tri-eq-lt k m h0) refl) 
    (λ h0 → eq-trans _ (tri-eq-eq k m h0) refl) 
    (λ h0 → eq-trans _ (tri-eq-gt k m h0) refl)
termoid-val-subst F V k false s (fun f ts) = 
  cong (F f) (termoid-val-subst F V k true _ ts)

bct-iff-bct : ∀ b {R0 R1 F0 F1 V0 V1 f0 f1 g0 g1} → 
  ((R0 , F0 , V0 ⊨ f0) ↔ (R1 , F1 , V1 ⊨ f1)) →  
  ((R0 , F0 , V0 ⊨ g0) ↔ (R1 , F1 , V1 ⊨ g1)) →  
  ((R0 , F0 , V0 ⊨ bct b f0 g0) ↔ (R1 , F1 , V1 ⊨ bct b f1 g1)) 
bct-iff-bct or h0 h1  = or-iff-or h0 h1
bct-iff-bct and h0 h1 = and-iff-and h0 h1
bct-iff-bct imp h0 h1 = imp-iff-imp h0 h1
bct-iff-bct iff h0 h1 = iff-iff-iff h0 h1

qtf-iff-qtf : ∀ b {R0 R1 F0 F1 V0 V1 f0 f1} → 
  (∀ d → (R0 , F0 , (V0 / 0 ↦ d) ⊨ f0) ↔ (R1 , F1 , (V1 / 0 ↦ d) ⊨ f1)) →  
  ((R0 , F0 , V0 ⊨ qtf b f0) ↔ (R1 , F1 , V1 ⊨ qtf b f1))   
qtf-iff-qtf true h0 = ex-iff-ex h0
qtf-iff-qtf false h0 = fa-iff-fa h0

update-update : ∀ V k d e → ((V / 0 ↦ e ) / (suc k) ↦ d) ≡ ((V / k ↦ d) / 0 ↦ e) 
update-update V k d e = FX _ _ λ { 0 → refl ; (suc m) → refl }

termoid-val-incr : ∀ b F V d (t : Termoid b) → termoid-val F (V / 0 ↦ d) (incr-var t) ≡ termoid-val F V t 
termoid-val-incr false F V d (var k) = refl
termoid-val-incr false F V d (fun f ts) = 
  cong (F f) (termoid-val-incr true F V d ts)
termoid-val-incr true  F V d nil = refl
termoid-val-incr true  F V d (cons t ts) = 
  cong-2 _∷_ 
    (termoid-val-incr false F V d t) 
    (termoid-val-incr true F V d ts)

holds-subst : ∀ R F V k t f → 
  ((R , F , (V / k ↦ (term-val F V t)) ⊨ f) ↔ (R , F , V ⊨ subst-form k t f))
holds-subst R F V k t (rel r ts) = 
  eq-to-iff (\ x → T (R r x)) _ _ (termoid-val-subst F V k true _ ts)
holds-subst R F V k t (cst b) = ( id , id )
holds-subst R F V k t (not f) = iff-to-not-iff-not (holds-subst _ _ _ k t f)
holds-subst R F V k t (bct b f g) = 
  bct-iff-bct b (holds-subst _ _ _ k t f) (holds-subst _ _ _ k t g) 
holds-subst R F V k t (qtf b f) = 
  qtf-iff-qtf b 
    λ d →  
      eq-elim 
        (λ x → ((R , F , x ⊨ f) ↔ (R , F , V / 0 ↦ d ⊨ subst-form (suc k) (incr-var t) f))) 
        (update-update V k (term-val F V t) d) 
        ( eq-elim 
            ( λ x → 
                (R , F , (V / 0 ↦ d) / suc k ↦ x ⊨ f) ↔ 
                  (R , F , V / 0 ↦ d ⊨ subst-form (suc k) (incr-var t) f) ) 
            (termoid-val-incr false F V d t) 
            (holds-subst R F _ (suc k) (incr-var t) f) )

implies-c : ∀ t f → f => (apply-c t f) 
implies-c t (qtf false f) R F V h0 = fst (holds-subst R F V 0 t f) (h0 (term-val F V t))
implies-c t (not (qtf true f)) R F V h0 h1 = 
  h0 ((term-val F V t) , snd (holds-subst R F V 0 t f) h1) 
implies-c _ (cst _) _ _ _ _ = tt
implies-c _ (bct _ _ _) _ _ _ _ = tt
implies-c _ (qtf true _) _ _ _ _ = tt
implies-c _ (rel _ _) _ _ _ _ = tt
implies-c _ (not (cst _)) _ _ _ _ = tt
implies-c _ (not (bct _ _ _)) _ _ _ _ = tt
implies-c _ (not (qtf false _)) _ _ _ _ = tt
implies-c _ (not (rel _ _)) _ _ _ _ = tt
implies-c _ (not (not _)) _ _ _ _ = tt

implies-n : ∀ f → (f => apply-n f) 
implies-n (not (not f)) R F V = dne
implies-n (cst _) _ _ _ _ = tt
implies-n (rel _ _) _ _ _ _ = tt
implies-n (bct _ _ _) _ _ _ _ = tt
implies-n (qtf _ _) _ _ _ _ = tt
implies-n (not (cst _)) _ _ _ _ = tt
implies-n (not (rel _ _)) _ _ _ _ = tt
implies-n (not (bct _ _ _)) _ _ _ _ = tt
implies-n (not (qtf _ _)) _ _ _ _ = tt

prsv-a : ∀ B b k → sat B → sat (add B (apply-a b (nth k B))) 
prsv-a B false k h0 = prsv-implies B k (apply-a false) (λ f → fst (implies-a f)) h0 
prsv-a B true  k h0 = prsv-implies B k (apply-a true ) (λ f → snd (implies-a f)) h0 

term-val-update-par : ∀ F k d V → 
  term-val (F / nf k ↦f const-fun d) V (par k) ≡ d
term-val-update-par F k d V = 
  let h0 = tr-to-ite-eq {List D → D} {k =n k} {λ _ → d} {F (nf k)} (≡⇒≡ᵇ k _ refl) in
  eq-elim (λ x → x [] ≡ d) (eq-symm h0) refl 

ftr-eq-to-eq : ∀ f g → T (ftr-eq f g) → f ≡ g
ftr-eq-to-eq (nf k) (nf m) h0 = cong nf (≡ᵇ⇒≡ _ _ h0)
ftr-eq-to-eq (sf s) (sf t) h0 = cong sf (chars-eq-to-eq  _ _ h0)

good-to-ne-nf : ∀ k f → (good-ftr k f) → f ≠ nf k
good-to-ne-nf k (nf m) h0 h1 = 
  ex-falso h0 (eq-elim (λ x → ¬ (m < x)) (nf-inj h1) (<-irrefl refl))
good-to-ne-nf k (sf m) _ ()

good-ftr-to-eq : ∀ k r R rl → (good-ftr k r) → (R / (nf k) ↦r rl) r ≡ R r
good-ftr-to-eq k r R rl h0 = 
  ite-intro-lem {Rel} (ftr-eq (nf k) r) (λ x → x ≡ R r) 
        ( λ h1 → 
            let h2 = ftr-eq-to-eq (nf k) r h1 in 
            let h3 = good-to-ne-nf k r h0 in
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
    ( ite-intro-lem {Fun} (ftr-eq (nf k) f) (λ x → x ≡ F f) 
        ( λ h1 → 
            let h2 = eq-symm (ftr-eq-to-eq _ _ h1) in 
            let h3 : k < k  
                h3 = (fst (eq-elim {_} {f} {nf k} (λ x → good-termoid k (fun x ts)) h2 h0)) in
            ⊥-elim (<-irrefl refl h3) ) 
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
  eq-to-iff (λ (x : Rel) → T (x (termoid-val F V ts))) ((R / (nf k) ↦r rl) r) (R r) 
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
  eq-to-iff (λ x → T (R r x)) _ _ (good-to-termoid-val-eq F V k fn ts (snd h0)) 

prsv-d-aux : ∀ R F V k f → good-form k f → R , F , V ⊨ f → 
  ∃ λ d → R , F / (nf k) ↦f (const-fun d) , V ⊨ (apply-d k f) 
prsv-d-aux R F V k (qtf true f) h0 h1 = 
  ex-elim h1 λ d h2 → 
    let F' = (F / (nf k) ↦f (const-fun d)) in 
    d , 
      fst (holds-subst R F' V 0 (par k) f) 
      ( elim-eq-symm (λ x → R , F' , V / 0 ↦ x ⊨ f) 
          (snd (good-to-holds-update-iff _ _ _ _ _ f h0) h2) 
          (term-val-update-par F k d V) ) 
prsv-d-aux R F V k (not (qtf false f)) h0 h1 = 
  let h2 = not-fa-to-ex-not _ h1 in 
  ex-elim h2 λ d h3 → 
    let F' = (F / (nf k) ↦f (const-fun d)) in 
    d , 
      λ h4 → 
        let h5 = snd (holds-subst R F' V 0 (par k) f) h4 in 
        let h6 = fst (good-to-holds-update-iff R F _ k (const-fun d) f h0) h5 in 
        let h7 = eq-elim (λ x → R , F , V / 0 ↦ x ⊨ f) (term-val-update-par F k d V) h6 in 
        h3 h7
prsv-d-aux _ _ _ _ (cst _) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (rel _ _) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (bct _ _ _) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (qtf false _) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (not (cst _)) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (not (rel _ _)) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (not (bct _ _ _)) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (not (qtf true _)) _ _ = wit , tt 
prsv-d-aux _ _ _ _ (not (not _)) _ _ = wit , tt 

sats-to-sats-fa : ∀ R F V B f → good-bch B → 
  sats R F V B → sats R (F / (nf (size B)) ↦f f) V B
sats-to-sats-fa R F V B f h0 h1 g h2 = 
  snd (good-to-holds-update-iff R F V (size B) f g (h0 g h2)) (h1 g h2)

sats-to-sats-ra : ∀ R F V B r → good-bch B → 
  sats R F V B → sats (R / (nf (size B)) ↦r r) F V B
sats-to-sats-ra R F V B r h0 h1 f h2 = 
  snd (good-to-holds-ru-iff R F V (size B) r f (h0 f h2)) (h1 f h2)
  
prsv-d : ∀ B k → good-bch B → sat B → sat (add B (apply-d (size B) (nth k B))) 
prsv-d B k hB h0 = 
  ex-elim-3 h0 
    λ R F V (hR , hs) → 
      ex-elim
        ( prsv-d-aux R F V (size B) (nth k B) 
          (good-form-nth B k hB) 
          (sats-nth R F V B k hs) ) 
        λ d hd → 
          R , F / (nf (size B)) ↦f (const-fun d) , V , hR , 
            sats-add R _ V B _ (sats-to-sats-fa R F V B _ hB hs) hd 
      
prsv-n : ∀ B k → sat B → sat (add B (apply-n (nth k B)))
prsv-n B k h0 = prsv-implies B k apply-n implies-n h0

prsv-b : ∀ B k → sat B → 
  (sat (add B (fst (apply-b (nth k B)))) ∨ sat (add B (snd (apply-b (nth k B)))))
prsv-b B k h0 = 
  ex-elim-3 h0 
    λ R F V (hR , hB) → 
      let h1 = sats-nth R F V B k hB in 
      let h2 = implies-b (nth k B) R F V h1 in 
      or-elim h2 
        (intro-or-lft (λ h1 → R , F , V , hR , sats-add R F V B _ hB h1)) 
        (intro-or-rgt (λ h1 → R , F , V , hR , sats-add R F V B _ hB h1))

prsv-c : ∀ B t k → sat B → sat (add B (apply-c t (nth k B)))
prsv-c B t k h0 = prsv-implies B k (apply-c t) (implies-c t) h0 

prsv-s : ∀ B f → sat B → sat (add B (not f)) ∨ sat (add B f)
prsv-s B f h0 = 
  ex-elim-3 h0 λ R F V (hR , hs) → 
    elim-lem (R , F , V ⊨ f)  
      (λ h1 → or-rgt (R , F , V , hR , sats-add R F V B _ hs h1)) 
      (λ h1 → or-lft ((R , F , V , hR , sats-add R F V B _ hs h1))) 


termoid-eq-to-eq : ∀ {b} (t s : Termoid b) → T (termoid-eq t s) → t ≡ s
termoid-eq-to-eq nil nil _ = refl
termoid-eq-to-eq (cons t0 ts0) (cons t1 ts1) h0 = 
  let (h1 , h2) = tr-band-to-and (termoid-eq t0 _) _ h0 in 
  cong-2 cons (termoid-eq-to-eq _ _ h1) (termoid-eq-to-eq _ _ h2)
termoid-eq-to-eq (var k) (var m) h0 = cong var (≡ᵇ⇒≡ _ _ h0)
termoid-eq-to-eq (fun f0 ts0) (fun f1 ts1) h0 = 
  let (h1 , h2) = tr-band-to-and (ftr-eq f0 _) _ h0 in 
  cong-2 fun (ftr-eq-to-eq _ _ h1) (termoid-eq-to-eq _ _ h2)

terms-eq-to-eq : ∀ (t s : Terms) → T (terms-eq t s) → t ≡ s
terms-eq-to-eq = termoid-eq-to-eq {true}

bct-eq-to-eq : ∀ {b0 b1} → T (bct-eq b0 b1) → (b0 ≡ b1)
bct-eq-to-eq {or} {or} _ = refl
bct-eq-to-eq {and} {and} _ = refl
bct-eq-to-eq {imp} {imp} _ = refl
bct-eq-to-eq {iff} {iff} _ = refl

form-eq-to-eq : ∀ f g → T (form-eq f g) → f ≡ g
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

data mono-fun : Nat → Nat → Form → Set where
  mono-fun-fa : ∀ k m f → mono-fun k (suc m) f → mono-fun k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-fun-eq : ∀ k m f → good-ftr (suc k) f → 
    mono-fun k m ((fun f (mono-args-lft m)) =* (fun f (mono-args-rgt m)))

data mono-rel : Nat → Nat → Form → Set where
  mono-rel-fa : ∀ k m f → mono-rel k (suc m) f → mono-rel k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-rel-imp : ∀ k m r → good-ftr (suc k) r → 
    mono-rel k m ((rel r (mono-args-lft m)) →* (rel r (mono-args-rgt m)))

from-mono-args-equal-suc : ∀ V k → 
  mono-args-equal' (suc k) V → mono-args-equal' k V 
from-mono-args-equal-suc V k h0 m h1 = h0 m (<-trans h1 (n<sn _)) 

from-mono-args-equal-0 : ∀ F V k → mono-args-equal' k V → 
  (terms-val F V (mono-args-lft k) ≡ terms-val F V (mono-args-rgt k)) 
from-mono-args-equal-0 F V 0 _ = refl
from-mono-args-equal-0 F V (suc k) h0 = 
  cong-2 _∷_ (h0 k (n<sn _)) 
    (from-mono-args-equal-0 F V k (from-mono-args-equal-suc V k h0)) 

from-mono-args-equal-1 : ∀ V k d → mono-args-equal' k V → 
  mono-args-equal' (suc k) ((V / 0 ↦ d) / 0 ↦ d) 
from-mono-args-equal-1 V k d h0 0 h1 = refl
from-mono-args-equal-1 V k d h0 (suc m) h1 = h0 m (s<s⇒< _ _ h1) 

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
  eq-elim (λ x → T (R r x)) (from-mono-args-equal-0 _ _ _ hE) h0

standard-to-holds-mono-rel : ∀ k f → mono-rel k 0 f → standard-to-holds f
standard-to-holds-mono-rel k f h0 R F V hR = holds-mono-rel R F V k 0 f hR (λ _ ()) h0

standard-to-holds-mono-fun : ∀ k f → mono-fun k 0 f → standard-to-holds f
standard-to-holds-mono-fun k f h0 R F V hR = holds-mono-fun R F V k 0 f hR (λ _ ()) h0

standard-to-holds-top : standard-to-holds (cst true)
standard-to-holds-top R F V hR = tt

standard-to-holds-not-bot : standard-to-holds (not (cst false))
standard-to-holds-not-bot R F V hR = id

standard-to-sat : ∀ {B f} → standard-to-holds f → sat B → sat (add B f) 
standard-to-sat {B} {f} h0 = 
  ex-elim-3' 
    λ R F V (hR , hs) → R , F , V , hR , sats-add R F V B f hs (h0 R F V hR) 

ru-sf-eq : ∀ R k r s → (R / nf k ↦r r) (sf s) ≡ R (sf s)
ru-sf-eq R k r s = fs-to-ite-ne {Rel} {ftr-eq (nf k) (sf s)} {r} tt

standard-ru : ∀ R k rl → standard R → standard (R / (nf k) ↦r rl)
standard-ru R k rl h0 d0 d1 = 
  eq-elim (λ x → T (x _) ↔ (d0 ≡ d1)) (eq-symm (ru-sf-eq R k rl _)) (h0 _ _)

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

extend : List D → VA 
extend [] _ = wit
extend (d ∷ _) 0 = d
extend (_ ∷ ds) (suc k) = extend ds k

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

eq-va-lt : Nat → VA → VA → Set
eq-va-lt k V0 V1 = ∀ m → m < k → V0 m ≡ V1 m

eq-va-lt-suc : ∀ k V0 V1 d0 d1 → eq-va-lt k V0 V1 → d0 ≡ d1 → 
  eq-va-lt (suc k) (V0 / 0 ↦ d0) (V1 / 0 ↦ d1)
eq-va-lt-suc k V0 V1 d0 d1 h0 h1 0 h2 = h1
eq-va-lt-suc k V0 V1 d0 d1 h0 h1 (suc m) h2 = h0 m (s<s⇒< _ _ h2) 

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
  eq-to-iff (λ x → T (R r x)) (terms-val F V0 ts) _ (eq-va-lt-to-eq F V0 V1 k ts h0 h1)

eq-va-lt-symm : ∀ k V0 V1 → eq-va-lt k V0 V1 → eq-va-lt k V1 V0 
eq-va-lt-symm k V0 V1 h0 m h1 = eq-symm (h0 m h1)

eq-va-lt-extend-trunc : ∀ V k → eq-va-lt k (extend (trunc k V)) V
eq-va-lt-extend-trunc V 0 m ()
eq-va-lt-extend-trunc V (suc k) 0 h0 = refl
eq-va-lt-extend-trunc V (suc k) (suc m) h0 = eq-va-lt-extend-trunc (↓ V) k m (s<s⇒< _ _ h0)

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

def-rl-asc : RA → FA → Form → Rel
def-rl-asc R F f ds = rt (R , F , extend ds ⊨ f)

def-rl-desc : RA → FA → Form → Rel
def-rl-desc R F f ds = def-rl-asc R F f (reverse ds)

fa-update-eq : ∀ F k fn → fn ≡ (F / nf k ↦f fn) (nf k) 
fa-update-eq F k fn = 
  eq-symm (tr-to-ite-eq {_} {ftr-eq (nf k) (nf k)} (≡⇒≡ᵇ k _ refl)) 
 
ra-update-eq : ∀ R k r → (R / nf k ↦r r) (nf k) ≡ r
ra-update-eq R k r = (tr-to-ite-eq {_} {ftr-eq (nf k) (nf k)} (≡⇒≡ᵇ k _ refl)) 

data only-vars : ∀ {b} → Termoid b → Set where 
  only-vars-nil : only-vars nil
  only-vars-var : ∀ k → only-vars (var k)
  only-vars-cons : ∀ t ts → only-vars t → only-vars ts → only-vars (cons t ts)

only-vars-rev-terms : ∀ ts0 ts1 → only-vars ts0 → only-vars ts1 → only-vars (rev-terms ts0 ts1)
only-vars-rev-terms nil ts1 h0 h1 = h1
only-vars-rev-terms (cons t ts0) ts1 (only-vars-cons _ _ h0 h1) h2 = 
  only-vars-rev-terms ts0 (cons t ts1) h1 (only-vars-cons _ _ h0 h2)

only-vars-vars-desc : ∀ k → only-vars (vars-desc k)
only-vars-vars-desc 0 = only-vars-nil
only-vars-vars-desc (suc k) = only-vars-cons _ _ (only-vars-var k) (only-vars-vars-desc k)

only-vars-vars-asc : ∀ k → only-vars (vars-asc k)
only-vars-vars-asc k = only-vars-rev-terms (vars-desc k) nil (only-vars-vars-desc k) only-vars-nil 

only-vars-to-eq : ∀ {b} F0 F1 V (t : Termoid b) → only-vars t → termoid-val F0 V t ≡ termoid-val F1 V t
only-vars-to-eq F0 F1 V nil _ = refl
only-vars-to-eq F0 F1 V (var _) _ = refl
only-vars-to-eq F0 F1 V (cons t ts) (only-vars-cons _ _ h0 h1) = 
  cong-2 _∷_ (only-vars-to-eq _ _ _ t h0) (only-vars-to-eq _ _ _ ts h1)

val-vars-asc-eq : ∀ F0 F1 V k → termoid-val F0 V (vars-asc k) ≡ termoid-val F1 V (vars-asc k) 
val-vars-asc-eq F0 F1 V k = only-vars-to-eq _ _ _ _  (only-vars-vars-asc k)

val-vars-desc-eq : ∀ F0 F1 V k → termoid-val F0 V (vars-desc k) ≡ termoid-val F1 V (vars-desc k) 
val-vars-desc-eq F0 F1 V k = only-vars-to-eq _ _ _ _  (only-vars-vars-desc k)

skm-fun-desc-reverse-trunc : ∀ R F V f k m →
  skm-fun-desc R F f (reverse (trunc m V)) ≡
    term-val (F / nf k ↦f skm-fun-desc R F f) V (skm-term-desc k m)
skm-fun-desc-reverse-trunc R F V f k m = 
  eq-trans _ 
    (cong (skm-fun-desc R F f) {reverse (trunc m V)} (reverse-trunc-eq-termoid-val-vars-desc F V m))
    ( cong-fun-arg {_} {_} {skm-fun-desc R F f} {_} 
        {termoid-val F V (vars-desc m)} {termoid-val _ V (vars-desc m)} 
        (fa-update-eq F k _) (val-vars-desc-eq _ _ V m) ) 

holds-extend-trunc-iff : ∀ R F V k f → vars-lt-form k f →  
  (R , F , extend (trunc k V) ⊨ f) ↔ (R , F , V ⊨ f)
holds-extend-trunc-iff R F V k f h0 = eq-va-lt-to-iff R F (extend (trunc k V)) V k f (eq-va-lt-extend-trunc V k) h0
  
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
  def-rl-asc R F f , λ V → iff-trans (T (def-rl-asc R F f ((trunc m V)))) 
    ( eq-to-iff-2 (λ x y → T (x y)) ((R / (nf k) ↦r _) (nf k)) (def-rl-asc R F f) _ (trunc m V) 
        (ra-update-eq R k _) (eq-symm (trunc-eq-termoid-val-vars-asc F V m)) ) 
    (iff-trans _ (tr-rt-iff) (iff-trans (R , F , V ⊨ f) 
  (holds-extend-trunc-iff R F V m f h1) (iff-symm  (good-to-holds-ru-iff R F V k  _ f h0))))
prsv-t-pred-def R F k m _ (pred-def-iff-desc k m f h0 h1) = 
  def-rl-desc R F f , λ V → iff-trans (T (def-rl-desc R F f (reverse (trunc m V)))) 
    (eq-to-iff-2 (λ x y → T (x y)) ((R / nf k ↦r _) (nf k))
      (def-rl-desc R F f) _ (reverse (trunc m V)) (ra-update-eq R k _) 
        (eq-symm (reverse-trunc-eq-termoid-val-vars-desc F V m))) (iff-trans _ tr-rt-iff 
          (iff-trans (R , F , extend (trunc m V) ⊨ f) 
            (eq-to-iff (λ x → R , F , extend x ⊨ f) _ (trunc m V) (reverse-reverse _)) 
            (iff-trans (R , F , V ⊨ f) (holds-extend-trunc-iff R F V m f h1) 
              ((iff-symm  (good-to-holds-ru-iff R F V k  _ f h0))))))
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

skm-fun-asc-aux : ∀ R F V k m f → good-form k f → 
  vars-lt-form (suc m) f → (R , F , V ⊨ ∃* f) → 
  R , (F / (nf k) ↦f skm-fun-asc R F f) , V ⊨ subst-form 0 (skm-term-asc k m) f
skm-fun-asc-aux R F V k m f hf h0 h1 = 
  fst (holds-subst R _ V 0 (skm-term-asc k m) f) 
    ( let h2 : R , F , extend (trunc m V) ⊨ ∃* f 
          h2 = fst (eq-va-lt-to-iff  R F _ (extend (trunc m V)) m (∃* f) (eq-va-lt-symm _ _ _ (eq-va-lt-extend-trunc V m)) h0) h1 in
      let h3 = extend-skm-fun-asc-holds R F f (trunc m V) h2 in 
      snd (good-to-holds-update-iff R F _ k _ f hf) 
       ( fst 
            ( eq-va-lt-to-iff R F _ _ (suc m) f 
                (eq-va-lt-suc m _ _ _ _ (eq-va-lt-extend-trunc V m)  (skm-fun-asc-trunc R F V f k m))
                h0 ) h3 )) 

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

prsv-t : ∀ B f → good-bch B → jst (size B) f → sat B → sat (add B f)
prsv-t _ _ _ (jst-top _) = standard-to-sat standard-to-holds-top
prsv-t _ _ _ (jst-not-bot _) = standard-to-sat standard-to-holds-not-bot
prsv-t _ _ _ (jst-refl _) = standard-to-sat standard-to-holds-refl
prsv-t _ _ _ (jst-symm _) = standard-to-sat standard-to-holds-symm
prsv-t _ _ _ (jst-trans _) = standard-to-sat standard-to-holds-trans
prsv-t _ _ _ (jst-fun k f h0) = standard-to-sat (standard-to-holds-mono-fun k f h0)
prsv-t _ _ _ (jst-rel k f h0) = standard-to-sat (standard-to-holds-mono-rel k f h0)
prsv-t B f hB (jst-choice k f h0) = 
  ex-elim-3' 
    λ R F V (h1 , h2) → 
      ex-elim (prsv-t-choice R F (size B) 0 f h0) 
        λ fn h3 → 
          R , F / nf (size B) ↦f fn , V , h1 , 
            sats-add R _ V B f (sats-to-sats-fa R F V B fn hB h2) (h3 V)
prsv-t B f hB (jst-pred-def k f h0) = 
  ex-elim-3' λ R F V (h1 , h2) → 
    ex-elim (prsv-t-pred-def R F (size B) 0 f h0)
       λ r h3 → (R / nf (size B) ↦r r) , F , V ,  standard-ru R k r h1 , 
         sats-add _ F V B f (sats-to-sats-ra R F V B r hB h2) (h3 V) 

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
  (good-subst-form (skm-term-asc k m) f (suc k) 0 (n<sn _ , good-vars-asc _ m) (good-form-suc  _ f h0))
good-choice k m _ (choice-imp-desc k m f h0 h1) = (good-form-suc _ f h0) , 
  ((good-subst-form (skm-term-desc k m) f (suc k) 0 (n<sn _ , good-vars-desc _ m) (good-form-suc  _ f h0)))

good-pred-def : ∀ k m f → pred-def k m f → good-form (suc k) f
good-pred-def k m _ (pred-def-fa k m f h0) = good-pred-def k _ f h0
good-pred-def k m _ (pred-def-iff-asc k m f h0 h1) = (n<sn _ , (good-vars-asc _ m)) , (good-form-suc _ f h0)
good-pred-def k m _ (pred-def-iff-desc k m f h0 h1) = 
 (n<sn _ , (good-vars-desc _ m)) , (good-form-suc _ f h0)

good-bch-t : ∀ B g → jst (size B) g → good-bch B → good-bch (add B g)
good-bch-t B _ (jst-top _) h0           = good-bch-add B _ h0 tt 
good-bch-t B _ (jst-not-bot _) h0       = good-bch-add B _ h0 tt
good-bch-t B _ (jst-refl _) h0          = good-bch-add B _ h0 (tt , tt , tt , tt )
good-bch-t B _ (jst-symm _) h0          = good-bch-add B _ h0 ((tt , tt , tt , tt) , (tt , tt , tt , tt))
good-bch-t B _ (jst-trans _) h0         = good-bch-add B _ h0 ((tt , tt , tt , tt), (tt , tt , tt , tt) , (tt , tt , tt , tt))
good-bch-t B _ (jst-fun k f hm) h0      = good-bch-add B _ h0 (good-mono-fun k 0 f hm)
good-bch-t B _ (jst-rel k f hm) h0      = good-bch-add B _ h0 (good-mono-rel k 0 f hm)
good-bch-t B _ (jst-choice k f hc) h0   = good-bch-add B _ h0 (good-choice (size B) 0 _ hc) 
good-bch-t B _ (jst-pred-def k f hp) h0 = good-bch-add B _ h0 (good-pred-def (size B) 0 _ hp) 

from-chks-mono-fun : ∀ k m f → T (chk-mono-fun k m f) → mono-fun k m f
from-chks-mono-fun k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) h0 = 
  let h1 = from-chks-mono-fun k (suc m) f (bsnd (c =c '=') _ h0) in 
  let h2 = char-eq-to-eq _ _ (bfst (c =c '=') _ h0) in 
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
    (mono-fun-eq k m f0 (chks-good-ftr (suc k) f0 h2))

from-chks-mono-rel : ∀ k m f → T (chk-mono-rel k m f) → mono-rel k m f
from-chks-mono-rel k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) h0 = 
  let h1 = from-chks-mono-rel k (suc m) f (bsnd (c =c '=') _ h0) in 
  let h2 = char-eq-to-eq _ _ (bfst (c =c '=') _ h0) in 
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
    (mono-rel-imp k m r0 (chks-good-ftr (suc k) r0 h1))

from-chks-vars-lt-termoid : ∀ {b} k (t : Termoid b) → T (chk-vars-lt-termoid k t) → vars-lt-termoid k t
from-chks-vars-lt-termoid k nil h0 = tt
from-chks-vars-lt-termoid k (cons t ts) h0 = 
  let (h1 , h2) = tr-band-to-and _ _ h0 in 
  from-chks-vars-lt-termoid k t h1 , from-chks-vars-lt-termoid k ts h2
from-chks-vars-lt-termoid k (var m) h0 = <ᵇ⇒< _ _ h0 
from-chks-vars-lt-termoid k (fun _ ts) h0 = from-chks-vars-lt-termoid k ts h0

from-chks-vars-lt-form : ∀ k f → T (chk-vars-lt-form k f) → vars-lt-form k f
from-chks-vars-lt-form k (cst b) _ = tt
from-chks-vars-lt-form k (not f) h0 = from-chks-vars-lt-form k f h0
from-chks-vars-lt-form k (bct b f g) h0 = 
  let (h1 , h2) = tr-band-to-and _ _ h0 in 
  from-chks-vars-lt-form k f h1 , from-chks-vars-lt-form k g h2 
from-chks-vars-lt-form k (qtf _ f) h0 = from-chks-vars-lt-form (suc k) f h0
from-chks-vars-lt-form k (rel _ ts) h0 = from-chks-vars-lt-termoid k ts h0

from-chks-choice : ∀ k m f → T (chk-choice k m f) → choice k m f
from-chks-choice k m (qtf false f) h0 = choice-fa k m _ (from-chks-choice k (suc m) f h0)
from-chks-choice k m (bct imp (qtf true f) g) ht0 = 
  let (h1 , h2 , h3) = tr-band-to-and-3 (chk-good-form k f) _ _ ht0 in 
  let h4 = chks-good-form k f h1 in 
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

from-chks-pred-def : ∀ k m f → T (chk-pred-def k m f) → pred-def k m f
from-chks-pred-def k m (qtf false f) h0 = pred-def-fa k m _ (from-chks-pred-def k (suc m) f h0)
from-chks-pred-def k m (bct iff (rel (nf n) ts) f) h0 = 
  let (h1 , h2 , h3 , h4) = tr-band-to-and-4 (k =n n) (chk-good-form k f) (chk-vars-lt-form m f) _ h0 in 
  let h5 = ≡ᵇ⇒≡ k _ h1 in 
  let h6 = chks-good-form k f h2 in 
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

chks-jst : ∀ k f → T (chk-jst k f) → jst k f
chks-jst k f = 
  elim-bor (form-eq f (cst true)) _ 
    (λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (cst true) h0) (jst-top _)) 
    ( elim-bor (form-eq f (not (cst false))) _ 
      (λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (not (cst false)) h0) (jst-not-bot _)) 
      ( elim-bor (form-eq f _) _ 
        (λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (refl-axiom) h0) (jst-refl _))
        ( elim-bor (form-eq f symm-axiom) _ 
          (λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f (symm-axiom) h0) (jst-symm _)) 
          ( elim-bor (form-eq f trans-axiom) _
            (λ h0 → eq-elim-symm (jst k) (form-eq-to-eq f trans-axiom h0) (jst-trans _))
            ( elim-bor (chk-mono-rel k 0 f) _ 
              (λ h0 → jst-rel k f (from-chks-mono-rel k 0 f h0)) 
              ( elim-bor (chk-mono-fun k 0 f) _ 
                (λ h0 → jst-fun k f (from-chks-mono-fun k 0 f h0)) 
                ( elim-bor (chk-choice k 0 f) _ 
                  (λ h0 → jst-choice k f (from-chks-choice k 0 f h0))
                  (λ h0 → jst-pred-def k f (from-chks-pred-def k 0 f h0)) ) ) ) ) ) ) ) 

verify-correct : ∀ B p → good-bch B → T (verify B p) → unsat B
verify-correct B (rule-a k b p) hB hp hs = 
   verify-correct (add B _) p 
     (good-bch-a B k b hB) hp (prsv-a B b k hs) 
verify-correct B (rule-b k p q) hB hpq hs = 
  let (hp , hq) = tr-band-to-and (verify _ p) _ hpq in 
  let (h0 , h1) = good-bch-b B k hB in
  or-elim (prsv-b B k hs) 
    (verify-correct _ p h0 hp) 
    (verify-correct _ q h1 hq)
verify-correct B (rule-c k t p) hB hp hs = 
  let (hp0 , hp1) = tr-band-to-and (chk-good-term _ t) _ hp in 
  verify-correct (add B _) p 
    (good-bch-c B k t hB (chks-good-termoid _ t hp0)) 
    hp1 (prsv-c B t k hs)
verify-correct B (rule-d k p) hB hp hs = 
  verify-correct (add B _) p 
    (good-bch-d B k hB) hp (prsv-d B k hB hs)
verify-correct B (rule-n k p) hB hp hs = 
  verify-correct (add B _) p (good-bch-n B k  hB) hp (prsv-n B k hs)
verify-correct B (rule-s f p q) hB h0 hs = 
  let (h1 , hpq) = tr-band-to-and (chk-good-form _ f) _ h0 in 
  let (hp , hq) = tr-band-to-and (verify _ p) _ hpq in 
  let hg = chks-good-form _ f h1 in
  or-elim (prsv-s B f hs) 
    (verify-correct _ p (good-bch-add B (not f)  hB hg) hp) 
    ((verify-correct _ q (good-bch-add B f  hB hg) hq))
verify-correct B (rule-t f p) hB h0 hs = 
  let (h1 , hp) = tr-band-to-and (chk-jst _ f) _ h0 in 
  let hj = chks-jst (size B) f h1 in 
  verify-correct (add B f) p (good-bch-t B f hj  hB) hp (prsv-t B f hB hj hs)
verify-correct B (rule-x i j) hB hp hs = 
  ex-elim-3 hs 
    λ R F V (hR , hs) → 
    let h0 = form-eq-to-eq (nth i B) (not (nth j B)) hp in 
    let h1 = sats-nth R F V B i hs in 
    let h2 = sats-nth R F V B j hs in 
    elim-eq (λ x → R , F , V ⊨ x) h1 h0 h2

passes : ∀ {A : Set} → Read A → A → Set
passes r a = ∃ λ cs0 → ∃ λ cs1 → (r cs0) ≡ cont a cs1

returns : ∀ {A : Set} → Read A → Chars → A → Set
returns r cs a = ∃ λ cs' → (r cs) ≡ cont a cs'

is-cont : ∀ {A : Set} → Res A → Set
is-cont (stop _) = ⊥
is-cont (cont _ _) = ⊤

ends : ∀ {A : Set} → Read A → Set
ends r = ∃ λ cs → is-cont (r cs)

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

elim-seq-eq-just : ∀ {A B C : Set} (f : Read A) (g : Read B) cs0 csf b → 
  (∀ a cs1 → f cs0 ≡ cont a cs1 → g cs1 ≡ cont b csf → C) → 
  ((f >> g) cs0 ≡ cont b csf) → C
elim-seq-eq-just f g cs0 csf b h0 h1 with (f cs0)
... | cont a' cs1' = h0 a' cs1' refl h1 

elim-passes-seq : ∀ {A B C : Set} (f : Read A) (g : Read B) (b : B) → 
  (ends f → passes g b → C) → passes (f >> g) b → C
elim-passes-seq f g b h0 (cs0 , csf , h1) = 
  elim-seq-eq-just f g cs0 csf b 
    ( λ a cs1 h2 h3 → h0 (cs0 , eq-elim-symm is-cont h2 tt) (cs1 , csf , h3) ) 
    h1

elim-bind-eq-just : ∀ {A B C : Set} (f : Read A) (g : A → Read B) cs0 cs1 b → 
  (∀ a cs → (f cs0 ≡ cont a cs) → (g a cs ≡ cont b cs1) → C) → 
  ((f >>= g) cs0) ≡ cont b cs1 → C
elim-bind-eq-just f g cs0 csf b h0 h1 with (f cs0)
... | cont a cs1 = h0 a cs1 refl h1

elim-passes-bind : ∀ {A B C : Set} (f : Read A) (g : A → Read B) (b : B) → 
  (∀ a → passes f a → passes (g a) b → C) → passes (f >>= g) b → C
elim-passes-bind f g b h0 (cs0 , csf , h1) = 
  elim-bind-eq-just f g cs0 csf b 
    ( λ a cs1 h2 h3 → h0 a (cs0 , cs1 , h2) (cs1 , csf , h3)) h1

cont-inj-val : ∀ {A : Set} {a0 a1 : A} {st0 st1} → 
  cont a0 st0 ≡ cont a1 st1 → a0 ≡ a1 
cont-inj-val refl = refl

elim-passes-pass : ∀ {A B : Set} (a0 a1 : A) → 
  (a0 ≡ a1 → B) → passes (pass a0) a1 → B
elim-passes-pass a0 a1 h0 (cs0 , csf , h1) = h0 (cont-inj-val h1) 

elim-passes-fail : ∀ {A B : Set} (a : A) st → passes (fail st) a → B
elim-passes-fail _ _ (_ , _ , ()) 

from-ends-pass-if : ∀ b → ends (pass-if b) → T b
from-ends-pass-if true _ = tt

best-form : Form → Set
best-form = good-form 0 

read-af-best : ∀ k f → passes (read-af k) f → best-form f
read-af-best k f = 
  elim-passes-seq (read-chars >> _) _ f 
    λ _ → 
      elim-passes-bind (read-form k) _ f
        λ g hg → 
          elim-passes-seq (pass-if (chk-good-form 0 g)) _ f 
            λ hg → 
              elim-passes-seq (read-spec-char _) _ f 
                λ _ → 
                  elim-passes-pass g f 
                    ( elim-eq (good-form 0) 
                      ( let h0 = from-ends-pass-if (chk-good-form 0 g) hg in 
                        chks-good-form 0 g h0 ) ) 

from-best-form : ∀ k f → best-form f → good-form k f
from-best-form 0 f = id
from-best-form (suc k) f h0 = 
  good-form-suc k f (from-best-form k f h0)

from-passes-read-bch-core : ∀ (B C : Bch) (k : Nat) → 
  good-bch B → passes (read-bch-core k B) C → good-bch C
from-passes-read-bch-core B C (suc k) hs hg = 
  elim-passes-alt (read-spec-char '.' >> pass B) _ C 
    ( elim-passes-seq (read-spec-char _) (pass B) C 
      λ _ → elim-passes-pass B C (elim-eq good-bch hs) ) 
    ( elim-passes-seq (read-spec-char _) _ C 
      λ _ → elim-passes-bind (read-af k) _ C 
        λ f hf hC → 
          let h0 = read-af-best k f hf in 
          from-passes-read-bch-core (add B f) C k 
            (good-bch-add B f hs (from-best-form _ f h0)) 
            hC ) 
    hg

from-passes-read-bch : ∀ (B : Bch) → passes read-bch B → good-bch B
from-passes-read-bch B h0 = 
  ex-elim-2 h0
    λ cs0 cs1 h1 →
      from-passes-read-bch-core nil B (length cs0) (λ _ ())
         (cs0 , cs1 , h1)

parse-verify-correct : ∀ cs-bch cs-prf → 
  T (parse-verify cs-bch cs-prf) → ∃ λ B → returns read-bch cs-bch B ∧ unsat B
parse-verify-correct cs-bch cs-prf = 
  intro-elim-res 
    (λ x → (T x → ∃ λ B → returns read-bch cs-bch B ∧ unsat B)) 
    (λ B _ → _) (λ _ → false) (read-bch cs-bch) 
    ( λ B cs0 hB → 
      intro-elim-res 
        (λ x → (T x → ∃ λ C → returns read-bch cs-bch C ∧ unsat C)) _ 
        (λ _ → false) (read-prf cs-prf) 
        ( λ p _ _ h0 → 
          B , (cs0 , hB) , 
            let h1 = from-passes-read-bch B (cs-bch , cs0 , hB) in 
            verify-correct B p h1 h0 ) 
        λ _ _ → ⊥-elim ) 
    λ _ _ → ⊥-elim