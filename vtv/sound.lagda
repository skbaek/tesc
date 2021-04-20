\documentclass{article}
\usepackage{agda}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage[verbose]{newunicodechar}
\input{unicode}
\begin{document}

\begin{code}
module sound (D : Set) (wit : D) where

open import Data.Empty
open import Relation.Nullary
open import Data.Unit.Base 
open import Data.Sum.Base
  using(_⊎_ ; inj₁ ; inj₂)
open import Data.Bool
  hiding (not)
  hiding (_<_)
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
open import Data.String 
  using (String)
open import basic 
  hiding (F)
open import verify 



-------- Semantics --------

\end{code}

%<*relfun>
\begin{code}
Rels : Set
Rels = List D → Bool
Funs : Set
Funs = List D → D
\end{code}
%</relfun>

%<*rafa>
\begin{code}
RA : Set 
RA = Functor → Rels 
FA : Set
FA = Functor → Funs
\end{code}
%</rafa>

%<*va>
\begin{code}
VA : Set 
VA = Nat → D
\end{code}
%</va>

\begin{code}
const-fun : D → Funs 
const-fun d _ = d
\end{code}

%<*termval>
\begin{code}
term-val : FA → VA → Term → D
terms-val : FA → VA → List Term → List D
term-val _ V (var k) = V k
term-val F V (fun f ts) = F f (terms-val F V ts)
terms-val F V [] = []
terms-val F V (t ∷ ts) = (term-val F V t) ∷ (terms-val F V ts)
\end{code} 
%</termval>

\begin{code}
↓ : VA → VA
↓ V k = V (suc k)

_/_↦r_ : RA → Functor → Rels → RA 
(R / f0 ↦r r) f1 = if (functor=? f0 f1) then r else R f1

_/_↦f_ : FA → Functor → Funs → FA 
(F / f0 ↦f f) f1 = if (functor=? f0 f1) then f else F f1

_/_↦_ : VA → Nat → D → VA 
(V / k ↦ d) m = tri k (V (pred m)) d (V m) m
_,_,_⊨_ : RA → FA → VA → Formula → Set
R , F , V ⊨ (cst b) = T b 
R , F , V ⊨ (not ϕ) = ¬ (R , F , V ⊨ ϕ)
R , F , V ⊨ (bct or ϕ ψ) = (R , F , V ⊨ ϕ) ⊎ (R , F , V ⊨ ψ)
R , F , V ⊨ (bct and ϕ ψ) = (R , F , V ⊨ ϕ) × (R , F , V ⊨ ψ)
R , F , V ⊨ (bct imp ϕ ψ) = (R , F , V ⊨ ϕ) → (R , F , V ⊨ ψ)
R , F , V ⊨ (bct iff ϕ ψ) = (R , F , V ⊨ ϕ) ↔ (R , F , V ⊨ ψ)
\end{code}

%<*qtf-val>
\begin{code}
R , F , V ⊨ (qtf false ϕ) = ∀ x → (R , F , (V / 0 ↦ x) ⊨ ϕ)
R , F , V ⊨ (qtf true ϕ) = ∃ λ x → (R , F , (V / 0 ↦ x) ⊨ ϕ)
\end{code}
%</qtf-val>

\begin{code}
R , F , V ⊨ (rel r ts) = T (R r (terms-val F V ts))
\end{code}

%<*respects-eq>
\begin{code}
respects-eq : RA → Set 
respects-eq R = ∀ x y → (T (R (plain [ '=' ]) (x ∷ y ∷ [])) ↔ (x ≡ y))
\end{code}
%</respects-eq>

%<*sat>
\begin{code}
satisfies : RA → FA → VA → Sequent → Set
satisfies R F V Γ = ∀ ϕ → ϕ ∈ Γ → R , F , V ⊨ ϕ
sat : Sequent → Set
sat Γ = ∃ λ R → ∃ λ F → ∃ λ V → (respects-eq R × satisfies R F V Γ)
unsat : Sequent → Set
unsat Γ = ¬ (sat Γ)
\end{code}
%</sat>

\begin{code}
_=>_ : Formula → Formula → Set 
f => g = ∀ R F V → (R , F , V ⊨ bct imp f g)



-------- nth --------

mem-nth : ∀ B k → (nth k B) ∈ B ⊎ (nth k B ≡ ⊤*)
mem-nth B k = or-elim (mem-lookup B k ⊤*) inj₁ inj₂

satisfies-nth : ∀ R F V B k → satisfies R F V B → R , F , V ⊨ nth k B
satisfies-nth R F V B k h0 = or-elim (mem-nth B k) (h0 _) 
  (eq-elim-symm (λ x → R , F , V ⊨ x) tt)



-------- Good --------

fi< : Nat → Functor → Set
fi< k (indexed m) = m < k 
fi< _ (plain _) = ⊤ 

term-lfi< : Nat → Term → Set
terms-lfi< : Nat → Terms → Set
term-lfi< _ (var _) = ⊤ 
term-lfi< k (fun f ts) = fi< k f × terms-lfi< k ts
terms-lfi< _ [] = ⊤ 
terms-lfi< k (t ∷ ts) = term-lfi< k t × terms-lfi< k ts 

formula-lfi< : Nat → Formula → Set
formula-lfi< _ (cst _) = ⊤
formula-lfi< k (rel r ts) = fi< k r × terms-lfi< k ts
formula-lfi< k (not f) = formula-lfi< k f
formula-lfi< k (bct _ f g) = formula-lfi< k f × formula-lfi< k g
formula-lfi< k (qtf _ f) = formula-lfi< k f

good : Sequent → Set
good B = ∀ f → f ∈ B → formula-lfi< (size B) f

fi<s : ∀ k f → fi< k f → fi< (suc k) f
fi<s k (indexed m) h = <-trans h (n<sn _) 
fi<s _ (plain _) _ = tt

term-lfi<s : ∀ k (t : Term) → term-lfi< k t → term-lfi< (suc k) t
terms-lfi<s : ∀ k (f : Terms) → terms-lfi< k f → terms-lfi< (suc k) f
term-lfi<s _ (var _) _ = tt 
term-lfi<s k (fun f ts) h0 = 
  fi<s k f (fst h0) , terms-lfi<s k ts (snd h0) 
terms-lfi<s _ [] _ = tt
terms-lfi<s k (t ∷ ts) h0 = 
  term-lfi<s _ t (fst h0) , terms-lfi<s k ts (snd h0)

formula-lfi<-suc : ∀ k f → formula-lfi< k f → formula-lfi< (suc k) f
formula-lfi<-suc k (cst _) h0 = tt 
formula-lfi<-suc k (rel r ts) h0 = 
   ( fi<s _ _ (fst h0) , 
     terms-lfi<s _ _ (snd h0) ) 
formula-lfi<-suc k (not f) h0 = formula-lfi<-suc k f h0
formula-lfi<-suc k (bct _ f g) h0 =
  (formula-lfi<-suc k f (fst h0)) , 
  (formula-lfi<-suc k g (snd h0))
formula-lfi<-suc k (qtf _ f) h0 = formula-lfi<-suc k f h0

good-add : ∀ B f → good B → formula-lfi< (suc (size B)) f → good (add B f)
good-add B f hB hf = 
  let heq = size-add B f in 
  all-add (formula-lfi< (size (add B f))) B f 
    (λ g hg → eq-elim-symm (λ x → formula-lfi< x g) (formula-lfi<-suc (size B) g (hB g hg)) heq)
    (eq-elim-symm (λ x → formula-lfi< x f) hf heq)
    
formula-lfi<-nth : ∀ B k → good B → formula-lfi< (size B) (nth k B)
formula-lfi<-nth B k h = or-elim (mem-nth B k) (h _) 
  λ h1 → eq-elim'-symm (formula-lfi< (size B)) h1 tt

subst-term-lfi< : ∀ s (t : Term) k m → term-lfi< k s → 
  term-lfi< k t → term-lfi< k (subst-term m s t)
subst-terms-lfi< : ∀ s (ts : Terms) k m → term-lfi< k s → 
  terms-lfi< k ts → terms-lfi< k (subst-terms m s ts)

subst-terms-lfi< _ [] _ _ _ _ = tt
subst-terms-lfi< s (t ∷ ts) k m h0 h1 = 
  (subst-term-lfi< s _ _ _ h0 (fst h1)) ,
  (subst-terms-lfi< s _ _ _ h0 (snd h1)) 
subst-term-lfi< s (var n) k m h0 h1 = 
  tri-intro-lem m n (term-lfi< k) (λ _ → tt) (λ _ → h0) (λ _ → tt)
subst-term-lfi< s (fun f ts) k m h0 h1 = 
  (fst h1) , (subst-terms-lfi< _ ts k m h0 (snd h1))

incr-var-term-lfi< : ∀ k (t : Term) → term-lfi< k t → term-lfi< k (incr-var-term t)
incr-var-terms-lfi< : ∀ k (ts : Terms) → terms-lfi< k ts → terms-lfi< k (incr-var-terms ts)
incr-var-terms-lfi< _ [] _ = tt
incr-var-terms-lfi< k (t ∷ ts) h = 
  (incr-var-term-lfi< _ t (fst h)) , (incr-var-terms-lfi< _ ts (snd h))
incr-var-term-lfi< k (var _) _ = tt
incr-var-term-lfi< k (fun f ts) h = 
  fst h , (incr-var-terms-lfi< _ ts (snd h))

subst-form-lfi< : ∀ t f k m → term-lfi< k t → formula-lfi< k f → formula-lfi< k (subst-form m t f)
subst-form-lfi< t (cst _) _ _ _ _ = tt
subst-form-lfi< t (rel r ts) k m h0 h1 = 
  fst h1 , subst-terms-lfi< t ts k m h0 (snd h1)
subst-form-lfi< t (not f) = subst-form-lfi< t f
subst-form-lfi< t (bct _ f g) k m h0 h1 = 
  (subst-form-lfi< t f k m h0 (fst h1)) , (subst-form-lfi< t g k m h0 (snd h1))
subst-form-lfi< t (qtf _ f) k m h0 h1 = 
  subst-form-lfi< (incr-var-term t) f k (suc m) (incr-var-term-lfi< _ _ h0) h1

par-lfi< : ∀ k → term-lfi< (suc k) (par k)
par-lfi< k = n<sn _ , tt

prsv-lfi<-a-core : ∀ k f → formula-lfi< k f → 
  (formula-lfi< k (analyze-a false f) × formula-lfi< k (analyze-a true f))
prsv-lfi<-a-core _ (cst _) _ = tt , tt 
prsv-lfi<-a-core k (bct and f g) = id
prsv-lfi<-a-core k (bct iff f g) (hf , hg) = (hf , hg) , (hg , hf) 
prsv-lfi<-a-core _ (bct or _ _) _ = tt , tt 
prsv-lfi<-a-core _ (bct imp _ _) _ = tt , tt 
prsv-lfi<-a-core _ (qtf _ _) _ = tt , tt 
prsv-lfi<-a-core _ (rel _ _) _ = tt , tt 
prsv-lfi<-a-core k (not (cst _)) _ =  tt , tt
prsv-lfi<-a-core k (not (bct or f g)) = id 
prsv-lfi<-a-core _ (not (bct and _ _)) _ = tt , tt 
prsv-lfi<-a-core k (not (bct imp f g)) = id
prsv-lfi<-a-core _ (not (bct iff _ _)) _ = tt , tt 
prsv-lfi<-a-core _ (not (qtf _ _)) _ = tt , tt 
prsv-lfi<-a-core _ (not (not _)) _ = tt , tt 
prsv-lfi<-a-core _ (not (rel _ _)) _ = tt , tt 

prsv-lfi<-a : ∀ k b f → formula-lfi< k f → formula-lfi< k (analyze-a b f)
prsv-lfi<-a k false f h0 = fst (prsv-lfi<-a-core k f h0)
prsv-lfi<-a k true  f h0 = snd (prsv-lfi<-a-core k f h0)

prsv-lfi<-b-core : ∀ k f → formula-lfi< k f → 
  (formula-lfi< k (analyze-b false f) × formula-lfi< k (analyze-b true f))
prsv-lfi<-b-core _ (cst _) _ = tt , tt 
prsv-lfi<-b-core k (bct or f g) = id
prsv-lfi<-b-core k (bct imp f g) = id 
prsv-lfi<-b-core _ (bct and _ _) _ = tt , tt 
prsv-lfi<-b-core _ (bct iff _ _) _ = tt , tt 
prsv-lfi<-b-core _ (qtf _ _) _ = tt , tt 
prsv-lfi<-b-core _ (rel _ _) _ = tt , tt 
prsv-lfi<-b-core k (not (cst _)) _ =  tt , tt
prsv-lfi<-b-core k (not (bct and f g)) = id 
prsv-lfi<-b-core _ (not (bct or _ _)) _ = tt , tt 
prsv-lfi<-b-core k (not (bct iff f g)) (hf , hg) = (hf , hg) , (hg , hf) 
prsv-lfi<-b-core _ (not (bct imp _ _)) _ = tt , tt 
prsv-lfi<-b-core _ (not (qtf _ _)) _ = tt , tt 
prsv-lfi<-b-core _ (not (not _)) _ = tt , tt 
prsv-lfi<-b-core _ (not (rel _ _)) _ = tt , tt 

prsv-lfi<-b : ∀ k b f → formula-lfi< k f → formula-lfi< k (analyze-b b f)
prsv-lfi<-b k false f h0 = fst (prsv-lfi<-b-core k f h0)
prsv-lfi<-b k true  f h0 = snd (prsv-lfi<-b-core k f h0)

prsv-lfi<-c : ∀ k t f → term-lfi< k t → formula-lfi< k f → formula-lfi< k (analyze-c t f)
prsv-lfi<-c k t (qtf false f) h0 h1 = subst-form-lfi< t f k 0 h0 h1 
prsv-lfi<-c k t (not (qtf true f)) h0 h1 = subst-form-lfi< t (not f) k 0 h0 h1 
prsv-lfi<-c _ _ (rel _ _) _ _ = tt
prsv-lfi<-c _ _ (bct _ _ _) _ _ = tt
prsv-lfi<-c _ _ (cst _) _ _ = tt
prsv-lfi<-c _ _ (qtf true _) _ _ = tt
prsv-lfi<-c _ _ (not (rel _ _)) _ _ = tt
prsv-lfi<-c _ _ (not (bct _ _ _)) _ _ = tt
prsv-lfi<-c _ _ (not (cst _)) _ _ = tt
prsv-lfi<-c _ _ (not (not _)) _ _ = tt
prsv-lfi<-c k t (not (qtf false _)) _ _ = tt

prsv-lfi<-d : ∀ k f → formula-lfi< k f → formula-lfi< (suc k) (analyze-d k f)
prsv-lfi<-d k (qtf true f) h0 = 
  subst-form-lfi< (par k) f (suc k) 0 (par-lfi< k) (formula-lfi<-suc k f h0)
prsv-lfi<-d k (not (qtf false f)) h0 = 
  subst-form-lfi< (par k) f (suc k) 0 (par-lfi< k) (formula-lfi<-suc k f h0)
prsv-lfi<-d k (cst _) h0 = tt
prsv-lfi<-d k (rel _ _) h0 = tt
prsv-lfi<-d k (bct _ _ _) h0 = tt
prsv-lfi<-d k (qtf false _) h0 = tt
prsv-lfi<-d k (not (cst _)) h0 = tt
prsv-lfi<-d k (not (rel _ _)) h0 = tt
prsv-lfi<-d k (not (bct _ _ _)) h0 = tt
prsv-lfi<-d k (not (not  _)) h0 = tt
prsv-lfi<-d k (not (qtf true _)) h0 = tt

prsv-lfi<-n : ∀ k f → formula-lfi< k f → formula-lfi< k (analyze-n f)
prsv-lfi<-n k (not (not f)) = id
prsv-lfi<-n _ (cst _) _ = tt
prsv-lfi<-n _ (rel _ _) _ = tt
prsv-lfi<-n _ (bct _ _ _) _ = tt
prsv-lfi<-n _ (qtf _ _) _ = tt
prsv-lfi<-n _ (not (cst _)) _ = tt
prsv-lfi<-n _ (not (rel _ _)) _ = tt
prsv-lfi<-n _ (not (bct _ _ _)) _ = tt
prsv-lfi<-n _ (not (qtf _ _)) _ = tt

good-a : ∀ B i b → good B → good (add B (analyze-a b (nth i B)))
good-a B i b h0  = 
  good-add B _ h0 
    ( formula-lfi<-suc _ (analyze-a b (nth i B)) 
      (prsv-lfi<-a _ b _ (formula-lfi<-nth B i h0)) )

good-b : ∀ B i b → good B → good (add B (analyze-b b (nth i B)))
good-b B i b h0  = 
  good-add B _ h0 
    ( formula-lfi<-suc _ (analyze-b b (nth i B)) 
      (prsv-lfi<-b _ b _ (formula-lfi<-nth B i h0)) )

good-c : ∀ B k t → good B → term-lfi< (suc (size B)) t → 
  (good (add B (analyze-c t (nth k B))))
good-c B k t h0 h2 = good-add B _ h0  
  (prsv-lfi<-c _ t (nth k B) h2 (formula-lfi<-suc _ (nth k B) (formula-lfi<-nth B k h0))) 

good-d : ∀ B k → good B → good (add B (analyze-d (size B) (nth k B)))
good-d B k h0 = 
  good-add B _ h0 (prsv-lfi<-d (size B) (nth k B) (formula-lfi<-nth B k h0))

good-n : ∀ B k → good B → good (add B (analyze-n (nth k B)))
good-n B k h0 = 
  good-add B _ h0 
    (prsv-lfi<-n _ (nth k B) (formula-lfi<-suc _ (nth k B) (formula-lfi<-nth _ _ h0)))  

fi<! : ∀ k f → T (fi<? k f) → fi< k f
fi<! k (indexed m) h = <ᵇ⇒< _ _ h 
fi<! _ (plain _) _ = tt

term-lfi<! : ∀ k (t : Term) → T (term-lfi<? k t) → term-lfi< k t 
terms-lfi<! : ∀ k (t : Terms) → T (terms-lfi<? k t) → terms-lfi< k t 

terms-lfi<! _ [] _ = tt
terms-lfi<! k (t ∷ ts) h0 = term-lfi<! _ _ (∧-lft  _ _ h0) , terms-lfi<! _ _ (∧-rgt _ _ h0)
term-lfi<! k (var m) h0 = tt
term-lfi<! k (fun f ts) h0 =
 fi<! _ _ (∧-lft  _ _ h0) , 
 terms-lfi<! _ _ (∧-rgt _ _ h0)

formula-lfi<! : ∀ k f → T (formula-lfi<? k f) → formula-lfi< k f  
formula-lfi<! _ (cst _) _ = tt
formula-lfi<! k (bct _ f g) h0 =  
  (formula-lfi<! k f (∧-lft  _ _ h0)) , 
  (formula-lfi<! k g (∧-rgt _ _ h0))
formula-lfi<! k (not f) h0 = formula-lfi<! k f h0
formula-lfi<! k (qtf _ f) h0 = formula-lfi<! k f h0
formula-lfi<! k (rel r ts) h0 = 
  fi<! _ r (∧-lft  _ _ h0) , 
  terms-lfi<! _ ts (∧-rgt _ _ h0) 

satisfies-add : ∀ R F V B f → satisfies R F V B → (R , F , V ⊨ f) → satisfies R F V (add B f)
satisfies-add R F V B f h0 h1 g h2 = or-elim (from-mem-add B g _ h2) (h0 _) (eq-elim-symm _ h1)

prsv-implies : ∀ B k (f : Formula → Formula) →
  (∀ g → g => f g) → sat B → sat (add B (f (nth k B))) 
prsv-implies B k f h0 h1 = 
  ex-elim-3 h1 
    λ R F V (h2 , h3) → 
      R , F , V , h2 , 
        λ g h4 → 
          or-elim (from-mem-add B g _ h4) (h3 g) 
            (eq-elim-symm (λ x → R , F , V ⊨ x) (h0 (nth k B) R F V (satisfies-nth R F V B k h3)))
  
implies-top : ∀ f → (f => ⊤*) 
implies-top _ _ _ _ _ = tt

implies-a : ∀ f → ((f => analyze-a false f) × (f => analyze-a true f))
implies-a f@(cst _) = implies-top f , implies-top f
implies-a (bct and f g) = (λ _ _ _ → fst) , (λ _ _ _ → snd)
implies-a (bct iff f g) = (λ _ _ _ → fst) , (λ _ _ _ → snd)
implies-a f@(bct or _ _) =  implies-top f , implies-top f
implies-a f@(bct imp _ _) = implies-top f , implies-top f
implies-a f@(qtf _ _) = implies-top f , implies-top f
implies-a f@(rel _ _) = implies-top f , implies-top f
implies-a f@(not (cst _)) = implies-top f , implies-top f
implies-a (not (bct or f g)) = (λ _ _ _ → not-inj₁) , (λ _ _ _ → not-inj₂)
implies-a f@(not (bct and _ _)) = implies-top f , implies-top f
implies-a (not (bct imp f g)) = (λ _ _ _ → not-imp-lft) , (λ _ _ _ → not-imp-rgt)
implies-a f@(not (bct iff _ _)) = implies-top f , implies-top f
implies-a f@(not (qtf _ _)) = implies-top f , implies-top f
implies-a f@(not (not _)) = implies-top f , implies-top f
implies-a f@(not (rel _ _)) = implies-top f , implies-top f

implies-b : ∀ f → f => ((analyze-b false f) ∨* (analyze-b true f))
implies-b (cst _) _ _ _ _ = inj₁ tt
implies-b (bct or f g) R F V = id
implies-b (bct imp f g) R F V = imp-to-not-or
implies-b (not (bct and f g)) _ _ _ = not-and-to-not-or-not
implies-b (not (bct iff f g)) _ _ _ = not-and-to-not-or-not
implies-b (not (bct or _ _)) _ _ _ _ = inj₁ tt
implies-b (not (bct imp _ _)) _ _ _ _ = inj₁ tt
implies-b (not (cst _)) _ _ _ _ = inj₁ tt
implies-b (not (qtf _ _)) _ _ _ _ = inj₁ tt
implies-b (not (not _)) _ _ _ _ = inj₁ tt
implies-b (not (rel _ _)) _ _ _ _ = inj₁ tt
implies-b (rel _ _) _ _ _ _ = inj₁ tt
implies-b (bct and _ _) _ _ _ _ = inj₁ tt
implies-b (bct iff _ _) _ _ _ _ = inj₁ tt
implies-b (qtf _ _) _ _ _ _ = inj₁ tt

term-val-subst : ∀ (F : FA) (V : VA) (k : Nat) (s : Term) (t : Term) → 
  (term-val F (V / k ↦ term-val F V s) t) ≡ (term-val F V (subst-term k s t))
terms-val-subst : ∀ (F : FA) (V : VA) (k : Nat) (s : Term) (t : Terms) → 
  (terms-val F (V / k ↦ term-val F V s) t) ≡ (terms-val F V (subst-terms k s t))

terms-val-subst F V k s [] = refl
terms-val-subst F V k s (t ∷ ts) = cong-2 _∷_ (term-val-subst F V k s t) (terms-val-subst F V k s ts)
term-val-subst F V k s (var m) = 
  tri-intro-lem k m 
    (λ x → (V / k ↦ term-val F V s) m ≡ term-val F V x)
    (λ h0 → eq-trans _ (tri-eq-lt k m h0) refl) 
    (λ h0 → eq-trans _ (tri-eq-eq k m h0) refl) 
    (λ h0 → eq-trans _ (tri-eq-gt k m h0) refl)
term-val-subst F V k s (fun f ts) = 
  cong (F f) (terms-val-subst F V k _ ts)

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

term-val-incr : ∀ F V d (t : Term) → term-val F (V / 0 ↦ d) (incr-var-term t) ≡ term-val F V t 
terms-val-incr : ∀ F V d (t : Terms) → terms-val F (V / 0 ↦ d) (incr-var-terms t) ≡ terms-val F V t 

term-val-incr F V d (var k) = refl
term-val-incr F V d (fun f ts) = cong (F f) (terms-val-incr F V d ts)
terms-val-incr F V d [] = refl
terms-val-incr F V d (t ∷ ts) = 
  cong-2 _∷_ 
    (term-val-incr F V d t) 
    (terms-val-incr F V d ts)

holds-subst : ∀ R F V k t f → 
  ((R , F , (V / k ↦ (term-val F V t)) ⊨ f) ↔ (R , F , V ⊨ subst-form k t f))
holds-subst R F V k t (rel r ts) = 
  eq-to-iff (λ x → T (R r x)) _ _ (terms-val-subst F V k _ ts)
holds-subst R F V k t (cst b) = ( id , id )
holds-subst R F V k t (not f) = iff-to-not-iff-not (holds-subst _ _ _ k t f)
holds-subst R F V k t (bct b f g) = 
  bct-iff-bct b (holds-subst _ _ _ k t f) (holds-subst _ _ _ k t g) 
holds-subst R F V k t (qtf b f) = 
  qtf-iff-qtf b 
    λ d →  
      eq-elim' 
        (λ x → ((R , F , x ⊨ f) ↔ (R , F , V / 0 ↦ d ⊨ subst-form (suc k) (incr-var-term t) f))) 
        (update-update V k (term-val F V t) d) 
        ( eq-elim' 
            ( λ x → 
                (R , F , (V / 0 ↦ d) / suc k ↦ x ⊨ f) ↔ 
                  (R , F , V / 0 ↦ d ⊨ subst-form (suc k) (incr-var-term t) f) ) 
            (term-val-incr F V d t) 
            (holds-subst R F _ (suc k) (incr-var-term t) f) )

implies-c : ∀ t f → f => (analyze-c t f) 
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

implies-n : ∀ f → (f => analyze-n f) 
implies-n (not (not f)) R F V = dne
implies-n (cst _) _ _ _ _ = tt
implies-n (rel _ _) _ _ _ _ = tt
implies-n (bct _ _ _) _ _ _ _ = tt
implies-n (qtf _ _) _ _ _ _ = tt
implies-n (not (cst _)) _ _ _ _ = tt
implies-n (not (rel _ _)) _ _ _ _ = tt
implies-n (not (bct _ _ _)) _ _ _ _ = tt
implies-n (not (qtf _ _)) _ _ _ _ = tt

prsv-a : ∀ B b k → sat B → sat (add B (analyze-a b (nth k B))) 
prsv-a B false k h0 = prsv-implies B k (analyze-a false) (λ f → fst (implies-a f)) h0 
prsv-a B true  k h0 = prsv-implies B k (analyze-a true ) (λ f → snd (implies-a f)) h0 

term-val-update-par : ∀ F k d V → term-val (F / indexed k ↦f const-fun d) V (par k) ≡ d
term-val-update-par F k d V = 
  let h0 = tr-to-ite-eq {List D → D} {k =n k} {λ _ → d} {F (indexed k)} (≡⇒≡ᵇ k _ refl) in
  eq-elim' (λ x → x [] ≡ d) (eq-symm h0) refl 

functor=! : ∀ f g → T (functor=? f g) → f ≡ g
functor=! (indexed k) (indexed m) h0 = cong indexed (≡ᵇ⇒≡ _ _ h0)
functor=! (plain s) (plain t) h0 = cong plain (chars=! _ _ h0)

lfi-lt-to-ne-nf : ∀ k f → (fi< k f) → f ≠ indexed k
lfi-lt-to-ne-nf k (indexed m) h0 h1 = 
  ex-falso h0 (eq-elim' (λ x → ¬ (m < x)) (nf-inj h1) (<-irrefl refl))
lfi-lt-to-ne-nf k (plain m) _ ()

fi<-to-eq : ∀ k r R rl → (fi< k r) → (R / (indexed k) ↦r rl) r ≡ R r
fi<-to-eq k r R rl h0 = 
  ite-intro-lem {Rels} (functor=? (indexed k) r) (λ x → x ≡ R r) 
        ( λ h1 → 
            let h2 = functor=! (indexed k) r h1 in 
            let h3 = lfi-lt-to-ne-nf k r h0 in
            ex-falso (eq-symm h2) h3 ) 
        λ _ → refl 

lfi-lt-to-term-val-eq : ∀ F V k fn (t : Term) → (term-lfi< k t) → 
  (term-val (F / indexed k ↦f fn) V t) ≡ (term-val F V t) 
lfi-lt-to-terms-val-eq : ∀ F V k fn (t : Terms) → (terms-lfi< k t) → 
  (terms-val (F / indexed k ↦f fn) V t) ≡ (terms-val F V t) 

lfi-lt-to-terms-val-eq F V k fn [] h0 = refl
lfi-lt-to-terms-val-eq F V k fn (t ∷ ts) h0 = 
  cong-2 _∷_
    (lfi-lt-to-term-val-eq F V k fn t (fst h0))  
    (lfi-lt-to-terms-val-eq F V k fn ts (snd h0))
lfi-lt-to-term-val-eq F V k fn (var m) h0 = refl
lfi-lt-to-term-val-eq F V k fn (fun f ts) h0 = 
  cong-2 {Funs} {List D} {D} (λ x y → x y) {(F / indexed k ↦f fn) f} {F f} 
    ( ite-intro-lem {Funs} (functor=? (indexed k) f) (λ x → x ≡ F f) 
        ( λ h1 → 
            let h2 = eq-symm (functor=! _ _ h1) in 
            let h3 : k < k  
                h3 = (fst (eq-elim' {_} {f} {indexed k} (λ x → term-lfi< k (fun x ts)) h2 h0)) in
            ⊥-elim (<-irrefl refl h3) ) 
        λ _ → refl )
    (lfi-lt-to-terms-val-eq F V k fn ts (snd h0))

lfi-lt-to-holds-ru-iff : ∀ R F V k r f → formula-lfi< k f → 
  ((R / indexed k ↦r r), F , V ⊨ f) ↔ (R , F , V ⊨ f)
lfi-lt-to-holds-ru-iff R F V k r (cst b) _ = iff-refl
lfi-lt-to-holds-ru-iff R F V k r (not f) h0 = 
  iff-to-not-iff-not (lfi-lt-to-holds-ru-iff R F V k r f h0)
lfi-lt-to-holds-ru-iff R F V k r (bct b f g) h0 = 
  bct-iff-bct b 
    (lfi-lt-to-holds-ru-iff R F V k r f (fst h0)) 
    (lfi-lt-to-holds-ru-iff R F V k r g (snd h0)) 
lfi-lt-to-holds-ru-iff R F V k r (qtf b f) h0 = 
  qtf-iff-qtf b 
    λ d → lfi-lt-to-holds-ru-iff R F _ k r f h0
lfi-lt-to-holds-ru-iff R F V k rl (rel r ts) h0 = 
  eq-to-iff (λ (x : Rels) → T (x (terms-val F V ts))) ((R / (indexed k) ↦r rl) r) (R r) 
    (fi<-to-eq k r R rl (fst h0))

lfi-lt-to-holds-update-iff : ∀ R F V k fn f → formula-lfi< k f → 
  (R , (F / indexed k ↦f fn), V ⊨ f) ↔ (R , F , V ⊨ f)
lfi-lt-to-holds-update-iff R F V k fn (cst b) _ = iff-refl
lfi-lt-to-holds-update-iff R F V k fn (not f) h0 = 
  iff-to-not-iff-not (lfi-lt-to-holds-update-iff R F V k fn f h0)
lfi-lt-to-holds-update-iff R F V k fn (bct b f g) h0 = 
  bct-iff-bct b 
    (lfi-lt-to-holds-update-iff R F V k fn f (fst h0)) 
    (lfi-lt-to-holds-update-iff R F V k fn g (snd h0)) 
lfi-lt-to-holds-update-iff R F V k fn (qtf b f) h0 = 
  qtf-iff-qtf b 
    λ d → lfi-lt-to-holds-update-iff R F _ k fn f h0
lfi-lt-to-holds-update-iff R F V k fn (rel r ts) h0 = 
  eq-to-iff (λ x → T (R r x)) _ _ (lfi-lt-to-terms-val-eq F V k fn ts (snd h0)) 

prsv-d-aux : ∀ R F V k f → formula-lfi< k f → R , F , V ⊨ f → 
  ∃ λ d → R , F / (indexed k) ↦f (const-fun d) , V ⊨ (analyze-d k f) 
prsv-d-aux R F V k (qtf true f) h0 h1 = 
  ex-elim h1 λ d h2 → 
    let F' = (F / (indexed k) ↦f (const-fun d)) in 
    d , 
      fst (holds-subst R F' V 0 (par k) f) 
      ( eq-elim-symm (λ x → R , F' , V / 0 ↦ x ⊨ f) 
          (snd (lfi-lt-to-holds-update-iff _ _ _ _ _ f h0) h2) 
          (term-val-update-par F k d V) ) 
prsv-d-aux R F V k (not (qtf false f)) h0 h1 = 
  let h2 = not-fa-to-ex-not _ h1 in 
  ex-elim h2 λ d h3 → 
    let F' = (F / (indexed k) ↦f (const-fun d)) in 
    d , 
      λ h4 → 
        let h5 = snd (holds-subst R F' V 0 (par k) f) h4 in 
        let h6 = fst (lfi-lt-to-holds-update-iff R F _ k (const-fun d) f h0) h5 in 
        let h7 = eq-elim' (λ x → R , F , V / 0 ↦ x ⊨ f) (term-val-update-par F k d V) h6 in 
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

satisfies-to-satisfies-fa : ∀ R F V B f → good B → 
  satisfies R F V B → satisfies R (F / (indexed (size B)) ↦f f) V B
satisfies-to-satisfies-fa R F V B f h0 h1 g h2 = 
  snd (lfi-lt-to-holds-update-iff R F V (size B) f g (h0 g h2)) (h1 g h2)

satisfies-to-satisfies-ra : ∀ R F V B r → good B → 
  satisfies R F V B → satisfies (R / (indexed (size B)) ↦r r) F V B
satisfies-to-satisfies-ra R F V B r h0 h1 f h2 = 
  snd (lfi-lt-to-holds-ru-iff R F V (size B) r f (h0 f h2)) (h1 f h2)
  
prsv-d : ∀ B k → good B → sat B → sat (add B (analyze-d (size B) (nth k B))) 
prsv-d B k hB h0 = 
  ex-elim-3 h0 
    λ R F V (hR , hs) → 
      ex-elim
        ( prsv-d-aux R F V (size B) (nth k B) 
          (formula-lfi<-nth B k hB) 
          (satisfies-nth R F V B k hs) ) 
        λ d hd → 
          R , F / (indexed (size B)) ↦f (const-fun d) , V , hR , 
            satisfies-add R _ V B _ (satisfies-to-satisfies-fa R F V B _ hB hs) hd 
      
prsv-n : ∀ B k → sat B → sat (add B (analyze-n (nth k B)))
prsv-n B k h0 = prsv-implies B k analyze-n implies-n h0

prsv-b : ∀ B k → sat B → 
  (sat (add B ((analyze-b false (nth k B)))) ⊎ sat (add B ((analyze-b true (nth k B)))))
prsv-b B k h0 = 
  ex-elim-3 h0 
    λ R F V (hR , hB) → 
      let h1 = satisfies-nth R F V B k hB in 
      let h2 = implies-b (nth k B) R F V h1 in 
      or-elim h2 
        (to-or-lft (λ h1 → R , F , V , hR , satisfies-add R F V B _ hB h1)) 
        (to-or-rgt (λ h1 → R , F , V , hR , satisfies-add R F V B _ hB h1))

prsv-c : ∀ B t k → sat B → sat (add B (analyze-c t (nth k B)))
prsv-c B t k h0 = prsv-implies B k (analyze-c t) (implies-c t) h0 

prsv-s : ∀ B f → sat B → sat (add B (not f)) ⊎ sat (add B f)
prsv-s B f h0 = 
  ex-elim-3 h0 λ R F V (hR , hs) → 
    lem-elim (R , F , V ⊨ f)  
      (λ h1 → inj₂ (R , F , V , hR , satisfies-add R F V B _ hs h1)) 
      (λ h1 → inj₁ ((R , F , V , hR , satisfies-add R F V B _ hs h1))) 

term=! : ∀ (t s : Term) → T (term=? t s) → t ≡ s
terms=! : ∀ (t s : Terms) → T (terms=? t s) → t ≡ s
terms=! [] [] _ = refl
terms=! (t0 ∷ ts0) (t1 ∷ ts1) h0 = 
  let (h1 , h2) = ∧⇒× (term=? t0 _) _ h0 in 
  cong-2 _∷_ (term=! _ _ h1) (terms=! _ _ h2)
term=! (var k) (var m) h0 = cong var (≡ᵇ⇒≡ _ _ h0)
term=! (fun f0 ts0) (fun f1 ts1) h0 = 
  let (h1 , h2) = ∧⇒× (functor=? f0 _) _ h0 in 
  cong-2 fun (functor=! _ _ h1) (terms=! _ _ h2)

bct=! : ∀ {b0 b1} → T (bct=? b0 b1) → (b0 ≡ b1)
bct=! {or} {or} _ = refl
bct=! {and} {and} _ = refl
bct=! {imp} {imp} _ = refl
bct=! {iff} {iff} _ = refl

formula=! : ∀ f g → T (formula=? f g) → f ≡ g
formula=! (cst b0) (cst b1) h0 = cong cst (biff-to-eq h0)
formula=! (not f0) (not f1) h0 = cong not (formula=! _ _ h0)
formula=! (bct b0 f0 g0) (bct b1 f1 g1) h0 = 
  let (h1 , h2 , h3) = ∧∧⇒×× _ _ _ h0 in
  cong-3 bct (bct=! h1) (formula=! f0 f1 h2) (formula=! _ _ h3)
formula=! (qtf b0 f0) (qtf b1 f1) h0 = 
  let (h1 , h2) = ∧⇒× _ _ h0 in
  cong-2 qtf (biff-to-eq h1) (formula=! _ _ h2)
formula=! (rel r0 ts0) (rel r1 ts1) h0 = 
  let (h1 , h2) = ∧⇒× _ _ h0 in
  cong-2 rel (functor=! _ _ h1) (terms=! _ _ h2)

respects-eq-to-holds : Formula → Set 
respects-eq-to-holds f = ∀ R F V → respects-eq R → R , F , V ⊨ f

respects-eq-to-holds-refl : respects-eq-to-holds refl-axiom
respects-eq-to-holds-refl R F V hR d = snd (hR d d) refl

respects-eq-to-holds-symm : respects-eq-to-holds symm-axiom
respects-eq-to-holds-symm R F V hR d0 d1 h0 = 
  snd (hR d1 d0) (eq-symm (fst (hR d0 d1) h0))

respects-eq-to-holds-trans : respects-eq-to-holds trans-axiom
respects-eq-to-holds-trans R F V hR d0 d1 d2 h0 h1 = 
  snd (hR d0 d2) (eq-trans d1 (fst (hR d0 d1) h0) (fst (hR d1 d2) h1))

mono-args-equal' : Nat → VA → Set
mono-args-equal' k V = ∀ m → m < k → V (suc (m * 2)) ≡ V (m * 2)

data mono-fun : Nat → Nat → Formula → Set where
  mono-fun-fa : ∀ k m f → mono-fun k (suc m) f → mono-fun k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-fun-eq : ∀ k m f → fi< (suc k) f → 
    mono-fun k m ((fun f (mono-args-lft m)) =* (fun f (mono-args-rgt m)))

data mono-rel : Nat → Nat → Formula → Set where
  mono-rel-fa : ∀ k m f → mono-rel k (suc m) f → mono-rel k m (∀* (∀* ((var 1 =* var 0) →* f)))
  mono-rel-imp : ∀ k m r → fi< (suc k) r → 
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

holds-mono-fun : ∀ R F V k m f → respects-eq R → 
  mono-args-equal' m V → mono-fun k m f → R , F , V ⊨ f 
holds-mono-fun R F V k m _ hR hE (mono-fun-fa k m f h0) d0 d1 h1 = 
  holds-mono-fun R F _ k (suc m) f hR 
    ( let h2 : d0 ≡ d1 
          h2 = (fst (hR d0 d1) h1) in 
      eq-elim' (λ x → mono-args-equal' (suc m) ((V / 0 ↦ d0) / 0 ↦ x)) 
        h2 ((from-mono-args-equal-1 V m d0 hE)))
    h0
holds-mono-fun R F V k m _ hR hE (mono-fun-eq k m f _) = 
  snd (hR _ _) (cong (F f) (from-mono-args-equal-0 F V m hE))

holds-mono-rel : ∀ R F V k m f → respects-eq R → 
  mono-args-equal' m V → mono-rel k m f → R , F , V ⊨ f 
holds-mono-rel R F V k m _ hR hE (mono-rel-fa k m f h0) d0 d1 h1 = 
  holds-mono-rel R F _ k (suc m) f hR 
    ( let h2 : d0 ≡ d1 
          h2 = (fst (hR d0 d1) h1) in 
      eq-elim' (λ x → mono-args-equal' (suc m) ((V / 0 ↦ d0) / 0 ↦ x)) 
        h2 (from-mono-args-equal-1 V m d0 hE) )
    h0
holds-mono-rel R F V k m _ hR hE (mono-rel-imp k m r _) h0 = 
  eq-elim' (λ x → T (R r x)) (from-mono-args-equal-0 _ _ _ hE) h0

respects-eq-to-holds-mono-rel : ∀ k f → mono-rel k 0 f → respects-eq-to-holds f
respects-eq-to-holds-mono-rel k f h0 R F V hR = holds-mono-rel R F V k 0 f hR (λ _ ()) h0

respects-eq-to-holds-mono-fun : ∀ k f → mono-fun k 0 f → respects-eq-to-holds f
respects-eq-to-holds-mono-fun k f h0 R F V hR = holds-mono-fun R F V k 0 f hR (λ _ ()) h0

respects-eq-to-holds-top : respects-eq-to-holds (cst true)
respects-eq-to-holds-top R F V hR = tt

respects-eq-to-holds-not-bot : respects-eq-to-holds (not (cst false))
respects-eq-to-holds-not-bot R F V hR = id

respects-eq-to-sat : ∀ {B f} → respects-eq-to-holds f → sat B → sat (add B f) 
respects-eq-to-sat {B} {f} h0 = 
  ex-elim-3' 
    λ R F V (hR , hs) → R , F , V , hR , satisfies-add R F V B f hs (h0 R F V hR) 

ru-sf-eq : ∀ R k r s → (R / indexed k ↦r r) (plain s) ≡ R (plain s)
ru-sf-eq R k r s = fs-to-ite-ne {Rels} {functor=? (indexed k) (plain s)} {r} tt

respects-eq-ru : ∀ R k rl → respects-eq R → respects-eq (R / (indexed k) ↦r rl)
respects-eq-ru R k rl h0 d0 d1 = 
  eq-elim' (λ x → T (x _) ↔ (d0 ≡ d1)) (eq-symm (ru-sf-eq R k rl _)) (h0 _ _)

term-vars< : Nat → Term → Set
terms-vars< : Nat → Terms → Set
term-vars< k (var m) = m < k
term-vars< k (fun _ ts) = terms-vars< k ts
terms-vars< _ [] = ⊤
terms-vars< k (t ∷ ts) = term-vars< k t × terms-vars< k ts 

formula-vars< : Nat → Formula → Set
formula-vars< k (rel _ ts) = terms-vars< k ts 
formula-vars< k (cst _) = ⊤
formula-vars< k (not f) = formula-vars< k f
formula-vars< k (bct _ f g) = formula-vars< k f × formula-vars< k g
formula-vars< k (qtf _ f) = formula-vars< (suc k) f 

data choice : Nat → Nat → Formula → Set where
  choice-fa : ∀ k m f → choice k (suc m) f → choice k m (∀* f)
  choice-imp-asc : ∀ k m f → formula-lfi< k f → formula-vars< (suc m) f → 
    choice k m ((∃* f) →* (subst-form 0 (skm-term-asc k m) f))
  choice-imp-desc : ∀ k m f → formula-lfi< k f → formula-vars< (suc m) f → 
    choice k m ((∃* f) →* (subst-form 0 (skm-term-desc k m) f))

data pred-def : Nat → Nat → Formula → Set where
  pred-def-fa : ∀ k m f → pred-def k (suc m) f → pred-def k m (∀* f)
  pred-def-iff-asc : ∀ k m f → formula-lfi< k f → formula-vars< m f →
    pred-def k m ((rel (indexed k) (vars-asc m)) ↔* f)  
  pred-def-iff-desc : ∀ k m f → formula-lfi< k f → formula-vars< m f →  
    pred-def k m ((rel (indexed k) (vars-desc m)) ↔* f)

data adm : Nat → Formula → Set where
  adm-top : ∀ k → adm k (cst true)
  adm-not-bot : ∀ k → adm k (not (cst false))
  adm-refl : ∀ k → adm k refl-axiom
  adm-symm : ∀ k → adm k symm-axiom
  adm-trans : ∀ k → adm k trans-axiom
  adm-fun : ∀ k f → mono-fun k 0 f → adm k f
  adm-rel : ∀ k f → mono-rel k 0 f → adm k f
  adm-choice : ∀ k f → choice k 0 f → adm k f
  adm-pred-def : ∀ k f → pred-def k 0 f → adm k f

extend : List D → VA 
extend [] _ = wit
extend (d ∷ _) 0 = d
extend (_ ∷ ds) (suc k) = extend ds k

skm-fun-asc : RA → FA → Formula → Funs
skm-fun-asc R F f ds = 
  lem-elim (R , F , extend ds ⊨ ∃* f) 
    (ex-elim' (λ d _ → d)) 
    (λ _ → wit)

skm-fun-desc : RA → FA → Formula → Funs
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

eq-va-lt-to-eq-term : ∀ F V0 V1 k (t : Term) → eq-va-lt k V0 V1 → 
  term-vars< k t → (term-val F V0 t) ≡ (term-val F V1 t) 
eq-va-lt-to-eq-terms : ∀ F V0 V1 k (t : Terms) → eq-va-lt k V0 V1 → 
  terms-vars< k t → (terms-val F V0 t) ≡ (terms-val F V1 t) 

eq-va-lt-to-eq-terms F V0 V1 k [] _ _ = refl
eq-va-lt-to-eq-terms F V0 V1 k (t ∷ ts) h0 h1 = 
  cong-2 _∷_ (eq-va-lt-to-eq-term F V0 V1 k t h0 (fst h1)) (eq-va-lt-to-eq-terms F V0 V1 k ts h0 (snd h1))
eq-va-lt-to-eq-term F V0 V1 k (var m) h0 h1 = h0 m h1
eq-va-lt-to-eq-term F V0 V1 k (fun f ts) h0 h1 = cong (F f) (eq-va-lt-to-eq-terms F V0 V1 k ts h0 h1)

eq-va-lt-to-iff : ∀ R F V0 V1 k f → eq-va-lt k V0 V1 → formula-vars< k f → 
  (R , F , V0 ⊨ f) ↔ (R , F , V1 ⊨ f) 
eq-va-lt-to-iff R F V0 V1 k (cst b) _ _ = iff-refl
eq-va-lt-to-iff R F V0 V1 k (not f) h0 h1 = iff-to-not-iff-not (eq-va-lt-to-iff R F V0 V1 k f h0 h1)
eq-va-lt-to-iff R F V0 V1 k (bct b f g) h0 h1 = 
  bct-iff-bct b (eq-va-lt-to-iff R F V0 V1 k f h0 (fst h1)) (eq-va-lt-to-iff R F V0 V1 k g h0 (snd h1))
eq-va-lt-to-iff R F V0 V1 k (qtf b f) h0 h1 = 
  qtf-iff-qtf b λ d → eq-va-lt-to-iff R F _ _ (suc k) f (eq-va-lt-suc k V0 V1 d d h0 refl) h1
eq-va-lt-to-iff R F V0 V1 k (rel r ts) h0 h1 = 
  eq-to-iff (λ x → T (R r x)) (terms-val F V0 ts) _ (eq-va-lt-to-eq-terms F V0 V1 k ts h0 h1)

eq-va-lt-symm : ∀ k V0 V1 → eq-va-lt k V0 V1 → eq-va-lt k V1 V0 
eq-va-lt-symm k V0 V1 h0 m h1 = eq-symm (h0 m h1)

eq-va-lt-extend-trunc : ∀ V k → eq-va-lt k (extend (trunc k V)) V
eq-va-lt-extend-trunc V 0 m ()
eq-va-lt-extend-trunc V (suc k) 0 h0 = refl
eq-va-lt-extend-trunc V (suc k) (suc m) h0 = eq-va-lt-extend-trunc (↓ V) k m (s<s⇒< _ _ h0)

extend-skm-fun-asc-holds : ∀ R F f ds → (R , F , extend ds ⊨ ∃* f) → 
  R , F , (extend ds) / 0 ↦ (skm-fun-asc R F f ds) ⊨ f  
extend-skm-fun-asc-holds R F f ds h0 = 
  lem-elim-intro-yes (λ x → R , F , extend ds / 0 ↦ x ⊨ f) 
    (λ (d , h1) → h1) 
    h0 

extend-skm-fun-desc-reverse-holds : ∀ R F f ds → (R , F , extend ds ⊨ ∃* f) → 
  R , F , (extend ds) / 0 ↦ (skm-fun-desc R F f (reverse ds)) ⊨ f  
extend-skm-fun-desc-reverse-holds R F f ds h0 = 
  let h1 = extend-skm-fun-asc-holds R F f ds h0 in 
  eq-elim'-symm (λ x → R , F , extend ds / 0 ↦ skm-fun-asc R F f x ⊨ f) (reverse-reverse ds) h1 

reverse-trunc-eq-terms-val-vars-desc-core : ∀ F V m → 
  terms-val F (↓ V) (vars-desc m) ∷ʳ V 0 ≡ terms-val F V (var m ∷ (vars-desc m))
reverse-trunc-eq-terms-val-vars-desc-core F V 0 = refl 
reverse-trunc-eq-terms-val-vars-desc-core F V (suc m) = cong-2 _∷_ refl (reverse-trunc-eq-terms-val-vars-desc-core F _ m) 

terms-val-rev-terms : ∀ F V ts0 ts1 → 
  terms-val F V (rev-terms ts0 ts1) ≡ reverseAcc (terms-val F V ts1) (terms-val F V ts0) 
terms-val-rev-terms F V [] ts1 = refl 
terms-val-rev-terms F V (t ∷ ts0) ts1 = terms-val-rev-terms F V ts0 (t ∷ ts1) 

reverse-trunc-eq-terms-val-vars-desc : ∀ F V m → reverse (trunc m V) ≡ terms-val F V (vars-desc m)
reverse-trunc-eq-terms-val-vars-desc F V 0 = refl
reverse-trunc-eq-terms-val-vars-desc F V (suc m) = eq-trans _ (reverse-cons (V 0) (trunc m (↓ V))) 
  (eq-trans ((terms-val F (↓ V) (vars-desc m)) ∷ʳ V 0) 
  (cong (λ x → x ∷ʳ V 0) (reverse-trunc-eq-terms-val-vars-desc F (↓ V) m)) (reverse-trunc-eq-terms-val-vars-desc-core F _ m))

def-rl-asc : RA → FA → Formula → Rels
def-rl-asc R F f ds = rt (R , F , extend ds ⊨ f)

def-rl-desc : RA → FA → Formula → Rels
def-rl-desc R F f ds = def-rl-asc R F f (reverse ds)

fa-update-eq : ∀ F k fn → fn ≡ (F / indexed k ↦f fn) (indexed k) 
fa-update-eq F k fn = 
  eq-symm (tr-to-ite-eq {_} {functor=? (indexed k) (indexed k)} (≡⇒≡ᵇ k _ refl)) 
 
ra-update-eq : ∀ R k r → (R / indexed k ↦r r) (indexed k) ≡ r
ra-update-eq R k r = (tr-to-ite-eq {_} {functor=? (indexed k) (indexed k)} (≡⇒≡ᵇ k _ refl)) 

data only-vars : Terms → Set where 
  only-vars-nil : only-vars []
  only-vars-cons : ∀ k ts → only-vars ts → only-vars ((var k) ∷ ts)

only-vars-rev-terms : ∀ ts0 ts1 → only-vars ts0 → only-vars ts1 → only-vars (rev-terms ts0 ts1)
only-vars-rev-terms [] ts1 h0 h1 = h1
only-vars-rev-terms ((var k) ∷ ts0) ts1 (only-vars-cons _ _ h0) h2 = 
  only-vars-rev-terms ts0 (var k ∷ ts1) h0 (only-vars-cons _ _ h2) 

only-vars-vars-desc : ∀ k → only-vars (vars-desc k)
only-vars-vars-desc 0 = only-vars-nil
only-vars-vars-desc (suc k) = only-vars-cons _ _ (only-vars-vars-desc k)

only-vars-vars-asc : ∀ k → only-vars (vars-asc k)
only-vars-vars-asc k = only-vars-rev-terms (vars-desc k) [] (only-vars-vars-desc k) only-vars-nil 

only-vars-to-eq : ∀ F0 F1 V (t : Terms) → only-vars t → terms-val F0 V t ≡ terms-val F1 V t
only-vars-to-eq F0 F1 V [] _ = refl
only-vars-to-eq F0 F1 V ((var k) ∷ ts) (only-vars-cons _ h0 h1) = 
  cong-2 _∷_ refl (only-vars-to-eq _ _ _ ts h1) 

val-vars-asc-eq : ∀ F0 F1 V k → terms-val F0 V (vars-asc k) ≡ terms-val F1 V (vars-asc k) 
val-vars-asc-eq F0 F1 V k = only-vars-to-eq _ _ _ _  (only-vars-vars-asc k)

val-vars-desc-eq : ∀ F0 F1 V k → terms-val F0 V (vars-desc k) ≡ terms-val F1 V (vars-desc k) 
val-vars-desc-eq F0 F1 V k = only-vars-to-eq _ _ _ _  (only-vars-vars-desc k)

skm-fun-desc-reverse-trunc : ∀ R F V f k m →
  skm-fun-desc R F f (reverse (trunc m V)) ≡
    term-val (F / indexed k ↦f skm-fun-desc R F f) V (skm-term-desc k m)
skm-fun-desc-reverse-trunc R F V f k m = 
  eq-trans _ 
    (cong (skm-fun-desc R F f) {reverse (trunc m V)} (reverse-trunc-eq-terms-val-vars-desc F V m))
    ( cong-fun-arg {_} {_} {skm-fun-desc R F f} {_} 
        {terms-val F V (vars-desc m)} {terms-val _ V (vars-desc m)} 
        (fa-update-eq F k _) (val-vars-desc-eq _ _ V m) ) 

holds-extend-trunc-iff : ∀ R F V k f → formula-vars< k f →  
  (R , F , extend (trunc k V) ⊨ f) ↔ (R , F , V ⊨ f)
holds-extend-trunc-iff R F V k f h0 = eq-va-lt-to-iff R F (extend (trunc k V)) V k f (eq-va-lt-extend-trunc V k) h0
  
trunc-eq-terms-val-vars-asc : ∀ F V m → (trunc m V) ≡ terms-val F V (vars-asc m)
trunc-eq-terms-val-vars-asc F V m = 
  reverse-inj _ _ 
    ( eq-trans _ (reverse-trunc-eq-terms-val-vars-desc F V m) 
        ( eq-trans _
            (eq-symm (reverse-reverse (terms-val F V (vars-desc m)))) 
            ( cong reverse {_} {terms-val F V (vars-asc m)} 
                (eq-symm (terms-val-rev-terms F V (vars-desc m) [])) ) ) )

rev-terms-lfi< : ∀ k ts0 ts1 → terms-lfi< k ts0 → terms-lfi< k ts1 → terms-lfi< k (rev-terms ts0 ts1)
rev-terms-lfi< k [] ts1 _ h0 = h0 
rev-terms-lfi< k (t ∷ ts0) ts1 (h0 , h1) h2 = rev-terms-lfi< k ts0 (t ∷ ts1) h1 (h0 , h2) 

vars-desc-lfi< : ∀ k m → terms-lfi< k (vars-desc m) 
vars-desc-lfi< k 0 = tt
vars-desc-lfi< k (suc m) = tt , (vars-desc-lfi< _ _)

vars-asc-lfi< : ∀ k m → terms-lfi< k (vars-asc m) 
vars-asc-lfi< k m = rev-terms-lfi< k (vars-desc m) [] (vars-desc-lfi< _ _) tt

skm-fun-desc-aux : ∀ R F V k m f → formula-lfi< k f → 
  formula-vars< (suc m) f → (R , F , V ⊨ ∃* f) → 
  R , (F / (indexed k) ↦f skm-fun-desc R F f) , V ⊨ subst-form 0 (skm-term-desc k m) f
skm-fun-desc-aux R F V k m f hf h0 h1 = 
  fst (holds-subst R _ V 0 (skm-term-desc k m) f) 
    (
      let h2 : R , F , extend (trunc m V) ⊨ ∃* f 
          h2 = fst (eq-va-lt-to-iff  R F _ (extend (trunc m V)) m (∃* f) (eq-va-lt-symm _ _ _ (eq-va-lt-extend-trunc V m)) h0) h1 in
      let h3 = extend-skm-fun-desc-reverse-holds R F f (trunc m V) h2 in 
      snd (lfi-lt-to-holds-update-iff R F _ k _ f hf) 
        ( fst 
            ( eq-va-lt-to-iff R F _ _ (suc m) f 
                (eq-va-lt-suc m _ _ _ _ (eq-va-lt-extend-trunc V m)  (skm-fun-desc-reverse-trunc R F V f k m))
                h0 ) h3 )
    )

prsv-t-pred-def : ∀ R F k m f → pred-def k m f → ∃ λ rl → ∀ V → (R / (indexed k) ↦r rl) , F , V ⊨ f 
prsv-t-pred-def R F k m _ (pred-def-fa k m f h0) = 
  ex-elim (prsv-t-pred-def R F k (suc m) f h0) λ r h1 → r , λ V d → h1 _
prsv-t-pred-def R F k m _ (pred-def-iff-asc k m f h0 h1) = 
  def-rl-asc R F f , λ V → iff-trans (T (def-rl-asc R F f ((trunc m V)))) 
    ( eq-to-iff-2 (λ x y → T (x y)) ((R / (indexed k) ↦r _) (indexed k)) (def-rl-asc R F f) _ (trunc m V) 
        (ra-update-eq R k _) (eq-symm (trunc-eq-terms-val-vars-asc F V m)) ) 
    (iff-trans _ (tr-rt-iff) (iff-trans (R , F , V ⊨ f) 
  (holds-extend-trunc-iff R F V m f h1) (iff-symm  (lfi-lt-to-holds-ru-iff R F V k  _ f h0))))
prsv-t-pred-def R F k m _ (pred-def-iff-desc k m f h0 h1) = 
  def-rl-desc R F f , λ V → iff-trans (T (def-rl-desc R F f (reverse (trunc m V)))) 
    (eq-to-iff-2 (λ x y → T (x y)) ((R / indexed k ↦r _) (indexed k))
      (def-rl-desc R F f) _ (reverse (trunc m V)) (ra-update-eq R k _) 
        (eq-symm (reverse-trunc-eq-terms-val-vars-desc F V m))) (iff-trans _ tr-rt-iff 
          (iff-trans (R , F , extend (trunc m V) ⊨ f) 
            (eq-to-iff (λ x → R , F , extend x ⊨ f) _ (trunc m V) (reverse-reverse _)) 
            (iff-trans (R , F , V ⊨ f) (holds-extend-trunc-iff R F V m f h1) 
              ((iff-symm  (lfi-lt-to-holds-ru-iff R F V k  _ f h0))))))
skm-fun-asc-trunc : ∀ R F V f k m →
  skm-fun-asc R F f (trunc m V) ≡
    term-val (F / indexed k ↦f skm-fun-asc R F f) V (skm-term-asc k m)
skm-fun-asc-trunc R F V f k m = 
  eq-trans _ 
    (cong (skm-fun-asc R F f) {trunc m V} (trunc-eq-terms-val-vars-asc F V m))
    ( cong-fun-arg {_} {_} {skm-fun-asc R F f} {_} 
        {terms-val F V (vars-asc m)} {terms-val _ V (vars-asc m)} 
        (fa-update-eq F k _) 
        (val-vars-asc-eq _ _ V m) )

skm-fun-asc-aux : ∀ R F V k m f → formula-lfi< k f → 
  formula-vars< (suc m) f → (R , F , V ⊨ ∃* f) → 
  R , (F / (indexed k) ↦f skm-fun-asc R F f) , V ⊨ subst-form 0 (skm-term-asc k m) f
skm-fun-asc-aux R F V k m f hf h0 h1 = 
  fst (holds-subst R _ V 0 (skm-term-asc k m) f) 
    ( let h2 : R , F , extend (trunc m V) ⊨ ∃* f 
          h2 = fst (eq-va-lt-to-iff  R F _ (extend (trunc m V)) m (∃* f) (eq-va-lt-symm _ _ _ (eq-va-lt-extend-trunc V m)) h0) h1 in
      let h3 = extend-skm-fun-asc-holds R F f (trunc m V) h2 in 
      snd (lfi-lt-to-holds-update-iff R F _ k _ f hf) 
       ( fst 
            ( eq-va-lt-to-iff R F _ _ (suc m) f 
                (eq-va-lt-suc m _ _ _ _ (eq-va-lt-extend-trunc V m)  (skm-fun-asc-trunc R F V f k m))
                h0 ) h3 )) 

prsv-t-choice : ∀ R F k m f → choice k m f → ∃ λ fn → ∀ V → R , F / (indexed k) ↦f fn , V ⊨ f 
prsv-t-choice R F k m _ (choice-fa k m f h0) = 
  ex-elim (prsv-t-choice R F k (suc m) f h0) λ fn h1 → fn , λ V d → h1 (V / 0 ↦ d)
prsv-t-choice R F k m _ (choice-imp-asc k m f h0 h1) = 
  skm-fun-asc R F f , λ V h2 → 
    let h3 : R , F , V ⊨ ∃* f 
        h3 = fst (lfi-lt-to-holds-update-iff R F V k _ (∃* f) h0) h2 in 
    skm-fun-asc-aux R _ V k m f h0 h1 h3 

prsv-t-choice R F k m _ (choice-imp-desc k m f h0 h1) = 
  skm-fun-desc R F f , λ V h2 → 
    let h3 : R , F , V ⊨ ∃* f 
        h3 = fst (lfi-lt-to-holds-update-iff R F V k _ (∃* f) h0) h2 in 
    skm-fun-desc-aux R _ V k m f h0 h1 h3 

prsv-t : ∀ B f → good B → adm (size B) f → sat B → sat (add B f)
prsv-t _ _ _ (adm-top _) = respects-eq-to-sat respects-eq-to-holds-top
prsv-t _ _ _ (adm-not-bot _) = respects-eq-to-sat respects-eq-to-holds-not-bot
prsv-t _ _ _ (adm-refl _) = respects-eq-to-sat respects-eq-to-holds-refl
prsv-t _ _ _ (adm-symm _) = respects-eq-to-sat respects-eq-to-holds-symm
prsv-t _ _ _ (adm-trans _) = respects-eq-to-sat respects-eq-to-holds-trans
prsv-t _ _ _ (adm-fun k f h0) = respects-eq-to-sat (respects-eq-to-holds-mono-fun k f h0)
prsv-t _ _ _ (adm-rel k f h0) = respects-eq-to-sat (respects-eq-to-holds-mono-rel k f h0)
prsv-t B f hB (adm-choice k f h0) = 
  ex-elim-3' 
    λ R F V (h1 , h2) → 
      ex-elim (prsv-t-choice R F (size B) 0 f h0) 
        λ fn h3 → 
          R , F / indexed (size B) ↦f fn , V , h1 , 
            satisfies-add R _ V B f (satisfies-to-satisfies-fa R F V B fn hB h2) (h3 V)
prsv-t B f hB (adm-pred-def k f h0) = 
  ex-elim-3' λ R F V (h1 , h2) → 
    ex-elim (prsv-t-pred-def R F (size B) 0 f h0)
       λ r h3 → (R / indexed (size B) ↦r r) , F , V ,  respects-eq-ru R k r h1 , 
         satisfies-add _ F V B f (satisfies-to-satisfies-ra R F V B r hB h2) (h3 V) 

mono-args-lft-lfi< : ∀ k m → terms-lfi< k (mono-args-lft m)
mono-args-lft-lfi< k 0 = tt
mono-args-lft-lfi< k (suc m) = tt , (mono-args-lft-lfi< k m)

mono-args-rgt-lfi< : ∀ k m → terms-lfi< k (mono-args-rgt m)
mono-args-rgt-lfi< k 0 = tt
mono-args-rgt-lfi< k (suc m) = tt , mono-args-rgt-lfi< k m

mono-fun-lfi< : ∀ k m f → mono-fun k m f → formula-lfi< (suc k) f
mono-fun-lfi< k m _ (mono-fun-fa k m f h0) = (tt , (tt , (tt , tt))) , (mono-fun-lfi< k _ f h0) 
mono-fun-lfi< k m _ (mono-fun-eq k m f h0) = tt , ((h0 , mono-args-lft-lfi< _ _) , (h0 , mono-args-rgt-lfi< _ _) , tt)

mono-rel-lfi< : ∀ k m f → mono-rel k m f → formula-lfi< (suc k) f
mono-rel-lfi< k m _ (mono-rel-fa k m f h0) = (tt , (tt , (tt , tt))) , (mono-rel-lfi< k _ f h0) 
mono-rel-lfi< k m _ (mono-rel-imp k m f h0) = (h0 , mono-args-lft-lfi< _ _) , (h0 , mono-args-rgt-lfi<  _ _)

choice-lfi< : ∀ k m f → choice k m f → formula-lfi< (suc k) f
choice-lfi< k m _ (choice-fa k m f h0) = choice-lfi< k _ f h0
choice-lfi< k m _ (choice-imp-asc k m f h0 h1) = (formula-lfi<-suc _ f h0) , 
  (subst-form-lfi< (skm-term-asc k m) f (suc k) 0 (n<sn _ , vars-asc-lfi< _ m) (formula-lfi<-suc  _ f h0))
choice-lfi< k m _ (choice-imp-desc k m f h0 h1) = (formula-lfi<-suc _ f h0) , 
  ((subst-form-lfi< (skm-term-desc k m) f (suc k) 0 (n<sn _ , vars-desc-lfi< _ m) (formula-lfi<-suc  _ f h0)))

pred-def-lfi< : ∀ k m f → pred-def k m f → formula-lfi< (suc k) f
pred-def-lfi< k m _ (pred-def-fa k m f h0) = pred-def-lfi< k _ f h0
pred-def-lfi< k m _ (pred-def-iff-asc k m f h0 h1) = (n<sn _ , (vars-asc-lfi< _ m)) , (formula-lfi<-suc _ f h0)
pred-def-lfi< k m _ (pred-def-iff-desc k m f h0 h1) = 
 (n<sn _ , (vars-desc-lfi< _ m)) , (formula-lfi<-suc _ f h0)

good-t : ∀ B g → adm (size B) g → good B → good (add B g)
good-t B _ (adm-top _) h0           = good-add B _ h0 tt 
good-t B _ (adm-not-bot _) h0       = good-add B _ h0 tt
good-t B _ (adm-refl _) h0          = good-add B _ h0 (tt , tt , tt , tt )
good-t B _ (adm-symm _) h0          = good-add B _ h0 ((tt , tt , tt , tt) , (tt , tt , tt , tt))
good-t B _ (adm-trans _) h0         = good-add B _ h0 ((tt , tt , tt , tt), (tt , tt , tt , tt) , (tt , tt , tt , tt))
good-t B _ (adm-fun k f hm) h0      = good-add B _ h0 (mono-fun-lfi< k 0 f hm)
good-t B _ (adm-rel k f hm) h0      = good-add B _ h0 (mono-rel-lfi< k 0 f hm)
good-t B _ (adm-choice k f hc) h0   = good-add B _ h0 (choice-lfi< (size B) 0 _ hc) 
good-t B _ (adm-pred-def k f hp) h0 = good-add B _ h0 (pred-def-lfi< (size B) 0 _ hp) 

mono-fun! : ∀ k m f → T (mono-fun? k m f) → mono-fun k m f
mono-fun! k m (qtf false (qtf false (bct imp (rel (plain (c ∷ [])) (var 1 ∷ (var 0 ∷ []))) f))) h0 = 
  let h1 = mono-fun! k (suc m) f (∧-rgt (c =c '=') _ h0) in 
  let h2 = char=! _ _ (∧-lft  (c =c '=') _ h0) in 
  eq-elim' 
    ( λ x →
        mono-fun k m
          (∀* (∀* (rel (plain (x ∷ [])) (var 1 ∷ (var zero ∷ [])) →* f))) )
    (eq-symm h2) (mono-fun-fa k m f h1) 
mono-fun! k m (rel (plain (c ∷ [])) (fun f0 ts0 ∷ (fun f1 ts1 ∷ []))) ht0 = 
  let (h1 , h2 , h3 , h4 , h5) = ∧∧∧∧⇒×××× (c =c '=') _ _ _ _ ht0 in 
  eq-elim'-4 (λ x y z w → mono-fun k m (rel (plain (x ∷ [])) (fun f0 y ∷ (fun z w ∷ []))))
    (eq-symm (char=! _ _ h1)) 
    (eq-symm (terms=! _ _ h4)) 
    (functor=! f0 f1 h3) 
    (eq-symm (terms=! _ _ h5)) 
    (mono-fun-eq k m f0 (fi<! (suc k) f0 h2))

mono-rel! : ∀ k m f → T (mono-rel? k m f) → mono-rel k m f
mono-rel! k m (qtf false (qtf false (bct imp (rel (plain (c ∷ [])) (var 1 ∷ (var 0 ∷ []))) f))) h0 = 
  let h1 = mono-rel! k (suc m) f (∧-rgt (c =c '=') _ h0) in 
  let h2 = char=! _ _ (∧-lft  (c =c '=') _ h0) in 
  eq-elim'
   ( λ x →
      mono-rel k m
            (∀* (∀* (rel (plain (x ∷ [])) (var 1 ∷ (var zero ∷ [])) →* f))) )
      (eq-symm h2) 
      (mono-rel-fa k m f h1) 
mono-rel! k m (bct imp (rel r0 ts0) (rel r1 ts1)) ht0 =  
  let (h1 , h2 , h3 , h4) = ∧∧∧⇒××× (fi<? (suc k) r0) _ _ _ ht0 in 
  eq-elim'-3 (λ x y z → mono-rel k m (rel r0 y →* rel x z)) 
    (functor=! r0 _ h2) 
    (eq-symm (terms=! _ _ h3)) -- (term*=! _ _ h3)) 
    (eq-symm (terms=! _ _ h4)) -- (term*=! _ _ h4)) 
    (mono-rel-imp k m r0 (fi<! (suc k) r0 h1))

term-vars<! : ∀ k (t : Term) → T (term-vars<? k t) → term-vars< k t
terms-vars<! : ∀ k (t : Terms) → T (terms-vars<? k t) → terms-vars< k t
term-vars<! k (var m) h0 = <ᵇ⇒< _ _ h0 
term-vars<! k (fun _ ts) h0 = terms-vars<! k ts h0
terms-vars<! k [] h0 = tt
terms-vars<! k (t ∷ ts) h0 = 
  let (h1 , h2) = ∧⇒× _ _ h0 in 
  term-vars<! k t h1 , terms-vars<! k ts h2

formula-vars<! : ∀ k f → T (formula-vars<? k f) → formula-vars< k f
formula-vars<! k (cst b) _ = tt
formula-vars<! k (not f) h0 = formula-vars<! k f h0
formula-vars<! k (bct b f g) h0 = 
  let (h1 , h2) = ∧⇒× _ _ h0 in 
  formula-vars<! k f h1 , formula-vars<! k g h2 
formula-vars<! k (qtf _ f) h0 = formula-vars<! (suc k) f h0
formula-vars<! k (rel _ ts) h0 = terms-vars<! k ts h0

choice! : ∀ k m f → T (choice? k m f) → choice k m f
choice! k m (qtf false f) h0 = choice-fa k m _ (choice! k (suc m) f h0)
choice! k m (bct imp (qtf true f) g) ht0 = 
  let (h1 , h2 , h3) = ∧∧⇒×× (formula-lfi<? k f) _ _ ht0 in 
  let h4 = formula-lfi<! k f h1 in 
  let hlt = formula-vars<! (suc m) f h2 in 
  ∨-elim (formula=? (subst-form 0 _ f) g) _ 
    ( λ h5 → 
        let h6 = formula=! (subst-form _ _ f) _ h5 in 
        eq-elim' (λ x → choice k m ((∃* f) →* x)) h6 
          (choice-imp-asc k m f h4 hlt) ) 
    ( λ h5 → 
        let h6 = formula=! (subst-form _ _ f) _ h5 in 
        eq-elim' (λ x → choice k m ((∃* f) →* x)) h6 
          (choice-imp-desc k m f h4 hlt) ) 
   h3

pred-def! : ∀ k m f → T (pred-def? k m f) → pred-def k m f
pred-def! k m (qtf false f) h0 = pred-def-fa k m _ (pred-def! k (suc m) f h0)
pred-def! k m (bct iff (rel (indexed n) ts) f) h0 = 
  let (h1 , h2 , h3 , h4) = ∧∧∧⇒××× (k =n n) (formula-lfi<? k f) (formula-vars<? m f) _ h0 in 
  let h5 = ≡ᵇ⇒≡ k _ h1 in 
  let h6 = formula-lfi<! k f h2 in 
  let h7 = formula-vars<! m f h3 in 
  ∨-elim (terms=? ts _) _ 
    ( λ h8 → 
        let h9 = eq-symm (terms=! ts _ h8) in 
        eq-elim'-2 (λ x y → pred-def k m (rel (indexed x) y ↔* f)) h5 h9 
          (pred-def-iff-asc k m f h6 h7) ) 
    ( λ h8 → 
        let h9 = eq-symm (terms=! ts _ h8) in 
        eq-elim'-2 (λ x y → pred-def k m (rel (indexed x) y ↔* f)) h5 h9 
          (pred-def-iff-desc k m f h6 h7) ) 
    h4

adm! : ∀ k f → T (adm? k f) → adm k f
adm! k f = 
  ∨-elim (formula=? f (cst true)) _ 
    (λ h0 → eq-elim'-symm (adm k) (formula=! f (cst true) h0) (adm-top _)) 
    ( ∨-elim (formula=? f (not (cst false))) _ 
      (λ h0 → eq-elim'-symm (adm k) (formula=! f (not (cst false)) h0) (adm-not-bot _)) 
      ( ∨-elim (formula=? f _) _ 
        (λ h0 → eq-elim'-symm (adm k) (formula=! f (refl-axiom) h0) (adm-refl _))
        ( ∨-elim (formula=? f symm-axiom) _ 
          (λ h0 → eq-elim'-symm (adm k) (formula=! f (symm-axiom) h0) (adm-symm _)) 
          ( ∨-elim (formula=? f trans-axiom) _
            (λ h0 → eq-elim'-symm (adm k) (formula=! f trans-axiom h0) (adm-trans _))
            ( ∨-elim (mono-rel? k 0 f) _ 
              (λ h0 → adm-rel k f (mono-rel! k 0 f h0)) 
              ( ∨-elim (mono-fun? k 0 f) _ 
                (λ h0 → adm-fun k f (mono-fun! k 0 f h0)) 
                ( ∨-elim (choice? k 0 f) _ 
                  (λ h0 → adm-choice k f (choice! k 0 f h0))
                  (λ h0 → adm-pred-def k f (pred-def! k 0 f h0)) ) ) ) ) ) ) ) 
\end{code}

%<*verify-sound>
\begin{code}
verify-sound : ∀ (S : Sequent) (p : Proof) → good S → T (verify S p) → unsat S
\end{code}
%</verify-sound>

\begin{code}
verify-sound B (rule-a k b p) hB hp hs = 
   verify-sound (add B _) p 
     (good-a B k b hB) hp (prsv-a B b k hs) 
verify-sound B (rule-b k p q) hB hpq hs = 
  let (hp , hq) = ∧⇒× (verify _ p) _ hpq in 
  or-elim (prsv-b B k hs) 
    (verify-sound _ p (good-b B k false hB) hp) 
    (verify-sound _ q (good-b B k true hB) hq)
verify-sound B (rule-c k t p) hB hp hs = 
  let (hp0 , hp1) = ∧⇒× (term-lfi<? _ t) _ hp in 
  verify-sound (add B _) p 
    (good-c B k t hB (term-lfi<! _ t hp0)) 
    hp1 (prsv-c B t k hs)
verify-sound B (rule-d k p) hB hp hs = 
  verify-sound (add B _) p 
    (good-d B k hB) hp (prsv-d B k hB hs)
verify-sound B (rule-n k p) hB hp hs = 
  verify-sound (add B _) p (good-n B k  hB) hp (prsv-n B k hs)
verify-sound B (rule-s f p q) hB h0 hs = 
  let (h1 , hpq) = ∧⇒× (formula-lfi<? _ f) _ h0 in 
  let (hp , hq) = ∧⇒× (verify _ p) _ hpq in 
  let hg = formula-lfi<! _ f h1 in
  or-elim (prsv-s B f hs) 
    (verify-sound _ p (good-add B (not f)  hB hg) hp) 
    ((verify-sound _ q (good-add B f  hB hg) hq))
verify-sound B (rule-t f p) hB h0 hs = 
  let (h1 , hp) = ∧⇒× (adm? _ f) _ h0 in 
  let hj = adm! (size B) f h1 in 
  verify-sound (add B f) p (good-t B f hj  hB) hp (prsv-t B f hB hj hs)
verify-sound B (rule-x i j) hB hp hs = 
  ex-elim-3 hs 
    λ R F V (hR , hs) → 
    let h0 = formula=! (nth i B) (not (nth j B)) hp in 
    let h1 = satisfies-nth R F V B i hs in 
    let h2 = satisfies-nth R F V B j hs in 
    eq-elim' (λ x → R , F , V ⊨ x) h0 h1 h2 

passes : ∀ {A : Set} → Parse A → A → Set
passes r a = ∃ λ cs0 → ∃ λ cs1 → (r cs0) ≡ cont a cs1

returns : ∀ {A : Set} → Parse A → Chars → A → Set
returns r cs a = ∃ λ cs' → (r cs) ≡ cont a cs'

is-cont : ∀ {A : Set} → Res A → Set
is-cont (stop _) = ⊥
is-cont (cont _ _) = ⊤

ends : ∀ {A : Set} → Parse A → Set
ends r = ∃ λ cs → is-cont (r cs)

alt-eq-cont-elim : ∀ {A C : Set} (f : Parse A) (g : Parse A) cs0 cs1 a → 
  (f cs0 ≡ cont a cs1 → C) → (g cs0 ≡ cont a cs1 → C) → 
  ((f <|> g) cs0 ≡ cont a cs1) → C
alt-eq-cont-elim f g cs0 cs1 a h0 h1 with (f cs0)
... | cont a' cs1' = h0 
... | stop _ = h1 

passes-alt-elim : ∀ {A C : Set} (f : Parse A) (g : Parse A) (a : A) → 
  (passes f a → C) → (passes g a → C) → passes (f <|> g) a → C
passes-alt-elim f g a h0 h1 (cs0 , csf , h2) = 
  alt-eq-cont-elim f g cs0 csf a 
    (λ h2 → h0 (cs0 , csf , h2)) 
    (λ h2 → h1 (cs0 , csf , h2)) 
    h2 

seq-eq-cont-elim : ∀ {A B C : Set} (f : Parse A) (g : Parse B) cs0 csf b → 
  (∀ a cs1 → f cs0 ≡ cont a cs1 → g cs1 ≡ cont b csf → C) → 
  ((f >> g) cs0 ≡ cont b csf) → C
seq-eq-cont-elim f g cs0 csf b h0 h1 with (f cs0)
... | cont a' cs1' = h0 a' cs1' refl h1 

passes-seq-elim : ∀ {A B C : Set} (f : Parse A) (g : Parse B) (b : B) → 
  (ends f → passes g b → C) → passes (f >> g) b → C
passes-seq-elim f g b h0 (cs0 , csf , h1) = 
  seq-eq-cont-elim f g cs0 csf b 
    ( λ a cs1 h2 h3 → h0 (cs0 , eq-elim'-symm is-cont h2 tt) (cs1 , csf , h3) ) 
    h1

bind-eq-cont-elim : ∀ {A B C : Set} (f : Parse A) (g : A → Parse B) cs0 cs1 b → 
  (∀ a cs → (f cs0 ≡ cont a cs) → (g a cs ≡ cont b cs1) → C) → 
  ((f >>= g) cs0) ≡ cont b cs1 → C
bind-eq-cont-elim f g cs0 csf b h0 h1 with (f cs0)
... | cont a cs1 = h0 a cs1 refl h1

passes-bind-elim : ∀ {A B C : Set} (f : Parse A) (g : A → Parse B) (b : B) → 
  (∀ a → passes f a → passes (g a) b → C) → passes (f >>= g) b → C
passes-bind-elim f g b h0 (cs0 , csf , h1) = 
  bind-eq-cont-elim f g cs0 csf b 
    ( λ a cs1 h2 h3 → h0 a (cs0 , cs1 , h2) (cs1 , csf , h3)) h1

cont-inj-val : ∀ {A : Set} {a0 a1 : A} {st0 st1} → 
  cont a0 st0 ≡ cont a1 st1 → a0 ≡ a1 
cont-inj-val refl = refl

passes-pass-elim : ∀ {A B : Set} (a0 a1 : A) → 
  (a0 ≡ a1 → B) → passes (pass a0) a1 → B
passes-pass-elim a0 a1 h0 (cs0 , csf , h1) = h0 (cont-inj-val h1) 

from-ends-pass-if : ∀ b → ends (pass-if b) → T b
from-ends-pass-if true _ = tt

parse-af-best : ∀ k f → passes (parse-af k) f → formula-lfi< 0 f
parse-af-best k f = 
  passes-seq-elim (parse-chars >> _) _ f 
    λ _ → 
      passes-bind-elim (parse-form k) _ f
        λ g hg → 
          passes-seq-elim (pass-if (formula-lfi<? 0 g)) _ f 
            λ hg → 
              passes-seq-elim (parse-spec-char _) _ f 
                λ _ → 
                  passes-pass-elim g f 
                    ( eq-elim (formula-lfi< 0) 
                      ( let h0 = from-ends-pass-if (formula-lfi<? 0 g) hg in 
                        formula-lfi<! 0 g h0 ) ) 

from-formula-lfi<0 : ∀ k f → formula-lfi< 0 f → formula-lfi< k f
from-formula-lfi<0 0 f = id
from-formula-lfi<0 (suc k) f h0 = 
  formula-lfi<-suc k f (from-formula-lfi<0 k f h0)

from-passes-parse-sequent-core : ∀ (B C : Sequent) (k : Nat) → 
  good B → passes (parse-sequent-core k B) C → good C
from-passes-parse-sequent-core B C (suc k) hs hg = 
  passes-alt-elim (parse-spec-char '.' >> pass B) _ C 
    ( passes-seq-elim (parse-spec-char _) (pass B) C 
      λ _ → passes-pass-elim B C 
        (eq-elim good hs) ) 
    ( passes-seq-elim (parse-spec-char _) _ C 
      λ _ → passes-bind-elim (parse-af k) _ C 
        λ f hf hC → 
          let h0 = parse-af-best k f hf in 
          from-passes-parse-sequent-core (add B f) C k 
            (good-add B f hs (from-formula-lfi<0 _ f h0)) 
            hC ) 
    hg

from-passes-parse-sequent : ∀ (B : Sequent) → passes parse-sequent B → good B
from-passes-parse-sequent B h0 = 
  ex-elim-2 h0
    λ cs0 cs1 h1 →
      from-passes-parse-sequent-core empty B (length cs0) (λ _ ())
         (cs0 , cs1 , h1)
\end{code}

%<*parse-verify-sound>
\begin{code}
parse-verify-sound : ∀ (seq-chars prf-chars : List Char) → 
  T (parse-verify seq-chars prf-chars) → 
  ∃ λ (S : Sequent) → returns parse-sequent seq-chars S × unsat S
\end{code}
%</parse-verify-sound>

\begin{code}
intro-elim-res : {A B : Set} (P : B → Set) (f : A → Chars → B) (g : String → B) (r : Res A) → 
  (∀ a cs → r ≡ (cont a cs) → P (f a cs)) → (∀ s → r ≡ (stop s) → P (g s)) → P (elim-res f g r)
intro-elim-res P f g (cont a cs) hf hg = hf _ _ refl
intro-elim-res P f g (stop s) hf hg = hg _ refl

parse-verify-sound cs-bch cs-prf = 
  intro-elim-res 
    (λ x → (T x → ∃ λ B → returns parse-sequent cs-bch B × unsat B)) 
    (λ B _ → _) (λ _ → false) (parse-sequent cs-bch) 
    ( λ B cs0 hB → 
      intro-elim-res 
        (λ x → (T x → ∃ λ C → returns parse-sequent cs-bch C × unsat C)) _ 
        (λ _ → false) (parse-prf cs-prf) 
        ( λ p _ _ h0 → 
          B , (cs0 , hB) , 
            let h1 = from-passes-parse-sequent B (cs-bch , cs0 , hB) in 
            verify-sound B p h1 h0 ) 
        λ _ _ → ⊥-elim ) 
    λ _ _ → ⊥-elim
\end{code}