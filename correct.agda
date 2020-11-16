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
open import definitions D wit

termoid-eq-to-eq : ∀ {b} (t s : Termoid b) → tr (termoid-eq t s) → t ≡ s
termoid-eq-to-eq = {!   !}

terms-eq-to-eq : ∀ (t s : Terms) → tr (terms-eq t s) → t ≡ s
terms-eq-to-eq = termoid-eq-to-eq {true}

form-eq-to-eq : ∀ f g → tr (form-eq f g) → f ≡ g
form-eq-to-eq f g h = {!   !}

from-chks-mono-fun : ∀ k m f → tr (chk-mono-fun k m f) → mono-fun k m f
from-chks-mono-fun k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) h0 = 
  let h1 = from-chks-mono-fun k (suc m) f (from-tr-band-rgt (c =c '=') _ h0) in 
  let h2 = char-eq-to-eq _ _ (from-tr-band-lft (c =c '=') _ h0) in 
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
    (mono-fun-eq k m f0 (from-chks-good-ftr k f0 h2))

from-chks-mono-rel : ∀ k m f → tr (chk-mono-rel k m f) → mono-rel k m f
from-chks-mono-rel k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) h0 = 
  let h1 = from-chks-mono-rel k (suc m) f (from-tr-band-rgt (c =c '=') _ h0) in 
  let h2 = char-eq-to-eq _ _ (from-tr-band-lft (c =c '=') _ h0) in 
  eq-elim 
    ( λ x →
        mono-rel k m
          (∀* (∀* (rel (sf (x ∷ [])) (cons (var 1) (cons (var zero) nil)) →* f))) )
    (eq-symm h2) (mono-rel-fa k m f h1) 
from-chks-mono-rel k m (bct imp (rel r0 ts0) (rel r1 ts1)) ht0 =  
  let (h1 , h2 , h3 , h4) = tr-band-to-and-4 (chk-good-ftr k r0) _ _ _ ht0 in 
  eq-elim-3 (λ x y z → mono-rel k m (rel r0 y →* rel x z)) 
    (ftr-eq-to-eq r0 _ h2) 
    (eq-symm (termoid-eq-to-eq _ _ h3)) 
    (eq-symm (termoid-eq-to-eq _ _ h4)) 
    (mono-rel-imp k m r0 (from-chks-good-ftr k r0 h1))

from-chks-vars-lt-form : ∀ k f → tr (chk-vars-lt-form k f) → vars-lt-form k f
from-chks-vars-lt-form  = {!   !}

from-chks-choice : ∀ k m f → tr (chk-choice k m f) → choice k m f
from-chks-choice k m (qtf false f) h0 = choice-fa k m _ (from-chks-choice k (suc m) f h0)
from-chks-choice k m (bct imp (qtf true f) g) ht0 = 
  let (h1 , h2 , h3) = tr-band-to-and-3 (chk-good-form k f) _ _ ht0 in 
  let h4 = from-chks-good-form k f h1 in 
  let hlt = from-chks-vars-lt-form (suc m) f h2 in 
  qix (form-eq (subst-form 0 _ f) g) _ 
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
  qix (terms-eq ts _) _ 
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
from-chks-jst k f = qix (form-eq f (cst true)) _ 
  ( λ h0 → eq-elim' (jst k) (form-eq-to-eq f (cst true) h0) (jst-top _)) 
    (qix (form-eq f (not (cst false))) _ 
    (λ h0 → eq-elim' (jst k) (form-eq-to-eq f (not (cst false)) h0) (jst-not-bot _)) 
    (qix (form-eq f _) _ 
      ((λ h0 → eq-elim' (jst k) (form-eq-to-eq f (refl-axiom) h0) (jst-refl _))) 
      (qix (form-eq f symm-axiom) _ (λ h0 → eq-elim' (jst k) (form-eq-to-eq f (symm-axiom) h0) (jst-symm _)) 
        (qix (form-eq f trans-axiom) _
 (λ h0 →
    eq-elim' (jst k) (form-eq-to-eq f trans-axiom h0) (jst-trans _))
   (qix (chk-mono-rel k 0 f) _ (λ h0 → jst-rel k f (from-chks-mono-rel k 0 f h0)) 
     (qix (chk-mono-fun k 0 f) _ (λ h0 → jst-fun k f (from-chks-mono-fun k 0 f h0)) 
       (qix (chk-choice k 0 f) _ 
         ((λ h0 → jst-choice k f (from-chks-choice k 0 f h0))) 
         (λ h0 → jst-pred-def k f (from-chks-pred-def k 0 f h0))))))))) -- or-elim' {! form-eq f (cst true) !} {!   !} {!   !}

from-passes-num-verify-t : ∀ B g → passes-num (verify-t B) g → jst (length B) g 
from-passes-num-verify-t B g (k , cs0 , csf , h0) = 
  use-bind-eq-just (read-form k) _ cs0 csf g h0 (λ f cs1 h1 h2 → 
    let (h3 , h4) = from-pass-if-seq-eq-just (chk-jst (length B) f) _ cs1 csf _ h2 in 
    let h5 = from-pass-eq-lft f g cs1 csf h4 in
    let h6 = from-chks-jst (length B) f h3 in 
    eq-elim (jst (length B)) h5 h6)

from-ends-verify-x : ∀ B → ends (verify-x B) → ∃ λ f → (f ∈ B) ∧ ((not f) ∈ B)
from-ends-verify-x = {!   !}

in-prob-cons : ∀ f P p → in-prob f P → in-prob f (p ∷ P) 
in-prob-cons f P p = ex-elim' λ nm h0 → (nm , or-rgt h0)

from-get-from-prob-eq : ∀ P nm0 cs0 cs1 f → 
  get-from-prob P nm0 cs0 ≡ just (f , cs1) → (in-prob f P) 
from-get-from-prob-eq ((nm1 , g) ∷ P) nm0 cs0 cs1 f = 
  intro-ite {_} {pass g} (nm1 =cs nm0)
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
    eq-elim (λ x → in-prob x P ∧ good-form (suc (length B)) x) h8 (h5 , from-chks-good-form _ f h6)

from-verify-p-eq-just : ∀ P B cs0 csf g → (verify-p P B cs0 ≡ just (g , csf)) → 
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