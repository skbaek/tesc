open import Agda.Builtin.Nat
  renaming (_<_ to _<n_)
  renaming (_==_ to _=n_)
open import Function.Base
open import Data.String 
  using (String)
  using (fromChar)
  using (_++_)
  using (concat)
open import Data.Bool
  hiding (not)
open import Data.Unit
open import Data.List
  renaming (lookup to lookup-list)
  renaming (concat to concat-list)
  renaming (_++_ to list-concat) 
  renaming (or to disj) 
  renaming (and to conj)
open import Agda.Builtin.Char
open import Data.Char
  renaming (_==_ to _=c_)
open import Data.Product
open import Data.Maybe.Base 
  renaming (_>>=_ to _o>=_)
  renaming (map to map?)
open import Agda.Builtin.Equality
open import basic
  hiding (F)

data Res (A : Set) : Set where
  cont : A → Chars → Res A 
  stop : String → Res A 

elim-res : {A B : Set} → (A → Chars → B) → (String → B) → (Res A) → B
elim-res f g (cont a cs) = f a cs
elim-res f g (stop s) = g s

intro-elim-res : {A B : Set} (P : B → Set) (f : A → Chars → B) (g : String → B) (r : Res A) → 
  (∀ a cs → r ≡ (cont a cs) → P (f a cs)) → (∀ s → r ≡ (stop s) → P (g s)) → P (elim-res f g r)
intro-elim-res P f g (cont a cs) hf hg = hf _ _ refl
intro-elim-res P f g (stop s) hf hg = hg _ refl

Read : Set → Set
Read A = Chars → Res A 

infixl 20 _>>=_ 

_>>=_ : ∀ {A} {B} → Read A → (A → Read B) → Read B
_>>=_ f g cs with f cs 
... | stop msg = stop msg
... | cont a cs' = g a cs'

_>>_ : ∀ {A} {B} → Read A → Read B → Read B
_>>_ f g cs with f cs 
... | stop msg = stop msg
... | cont _ cs' = g cs'

infixr 20 _<|>_ 

_<|>_ : ∀ {A} → Read A → Read A → Read A
_<|>_ f g cs with f cs 
... | stop _ = g cs
... | c = c

pass : {A : Set} → A → Read A
pass x cs = cont x cs 

fail : {A : Set} → String → Read A
fail s _ = stop s 

skip : Read ⊤
skip = pass tt



-------- Admissability Check --------

check-good-ftr : Nat → Functor → Bool
check-good-ftr k (nf m) = m <n k
check-good-ftr _ (sf _) = true

check-good-termoid : {b : Bool} → Nat → Termoid b → Bool
check-good-termoid k (var _) = true
check-good-termoid k (fun f ts) = check-good-ftr k f ∧ check-good-termoid k ts 
check-good-termoid k nil = true
check-good-termoid k (cons t ts) = check-good-termoid k t ∧ check-good-termoid k ts

check-good-term : Nat → Term → Bool
check-good-term = check-good-termoid 

check-good-terms : Nat → Terms → Bool
check-good-terms = check-good-termoid 

check-good-form : Nat → Formula → Bool
check-good-form k (cst _) = true
check-good-form k (rel r ts) = check-good-ftr k r ∧ check-good-terms k ts 
check-good-form k (not f) = check-good-form k f 
check-good-form k (qtf _ f) = check-good-form k f 
check-good-form k (bct _ f g) = check-good-form k f ∧ check-good-form k g

check-gnd-termoid : {b : Bool} → Nat → Termoid b → Bool
check-gnd-termoid k (var m) = m <n k 
check-gnd-termoid k (fun _ ts) = check-gnd-termoid k ts 
check-gnd-termoid k nil = true
check-gnd-termoid k (cons t ts) = check-gnd-termoid k t ∧ check-gnd-termoid k ts

check-gnd-term : Nat → Term → Bool
check-gnd-term = check-gnd-termoid 

check-gnd-terms : Nat → Terms → Bool
check-gnd-terms = check-gnd-termoid 

check-gnd-form : Nat → Formula → Bool
check-gnd-form k (cst _) = true
check-gnd-form k (rel _ ts) = check-gnd-terms k ts 
check-gnd-form k (not f) = check-gnd-form k f 
check-gnd-form k (qtf _ f) = check-gnd-form (suc k) f 
check-gnd-form k (bct _ f g) = check-gnd-form k f ∧ check-gnd-form k g



-------- Parsers --------

lift-read : {A : Set} → Maybe A → Read A 
lift-read nothing = fail "Cannot lift nothing" 
lift-read (just a) = pass a 

pass-if : Bool → Read ⊤
pass-if true = pass tt
pass-if false = fail "Pass-if test failed"

read-bool : Read Bool
read-bool ('0' ∷ cs) = cont false cs 
read-bool ('1' ∷ cs) = cont true cs 
read-bool _ = stop "Cannot read bool (head char neither '0' nor '1')" 

read-char : Read Char
read-char (c ∷ cs) = cont c cs
read-char = fail "Cannot read char from empty string" 

read-chars : Read Chars 
read-chars ('%' ∷ cs) = cont [] cs
read-chars (c ∷ cs) with read-chars cs 
... | cont cs0 cs1 = cont (c ∷ cs0) cs1
... | st = st 
read-chars = fail "read-char fail : reached end of input string before endmarker"

read-nat : Read Nat
read-nat = read-chars >>= (lift-read ∘ chars-to-nat)

_==c_ : Char → Char → Bool
_==c_ = primCharEquality

read-spec-char : Char → Read ⊤ 
read-spec-char c0 (c1 ∷ cs) = 
  if c0 ==c c1 
    then cont tt cs 
    else stop ("char expected = " ++ fromChar c0 ++ ", char read = " ++ fromChar c1)
read-spec-char _ = fail "read-spec-char fail : reached end of input string before endmarker"

read-ftr : Read Functor
read-ftr = 
  ( do read-spec-char '#' 
       k ← read-nat 
       pass (nf k) ) <|>
  ( do read-spec-char '"' 
       s ← read-chars 
       pass (sf s) ) 

read-termoid : ∀ b → Nat → Read (Termoid b)
read-termoid true _ ('.' ∷ cs) = cont nil cs 
read-termoid true (suc k) (',' ∷ cs) = ( do 
  t ← read-termoid false k 
  ts ← read-termoid true k
  pass (cons t ts) ) cs
read-termoid false _ ('#' ∷ cs) = ( do 
  k ← read-nat 
  pass (var k) ) cs 
read-termoid false (suc k) ('$' ∷ cs) = ( do 
  f ← read-ftr 
  ts ← read-termoid true k
  pass (fun f ts) ) cs 
read-termoid _ _ = fail "read-termoid fail" 

read-term : Nat → Read Term
read-term = read-termoid false

read-terms : Nat → Read Terms
read-terms = read-termoid true

read-qtf : Read Bool
read-qtf = 
  (read-spec-char '!' >> pass false) <|> (read-spec-char '?' >> pass true) 

read-bct : Read Bct
read-bct = 
  (read-spec-char '|' >> pass or) <|> 
  (read-spec-char '&' >> pass and) <|> 
  (read-spec-char '>' >> pass imp) <|> 
  (read-spec-char '=' >> pass iff) 

read-form : Nat → Read Formula
read-form (suc k) = 
  (read-bool >>= λ b → pass (cst b)) <|>
  ( do read-spec-char '$'
       f ← read-ftr 
       ts ← read-terms k
       pass (rel f ts) ) <|>
  ( do read-spec-char '~'
       f ← read-form k
       pass (not f) ) <|>
  ( do b ← read-qtf 
       f ← read-form k
       pass (qtf b f) ) <|>
  ( do b ← read-bct 
       f ← read-form k
       g ← read-form k
       pass (bct b f g) ) 
read-form 0 = fail "read-form fail"

read-af : Nat → Read Formula
read-af k =  do
  (read-chars >> (read-bool >>= pass-if)) 
  f ← read-form k 
  pass-if (check-good-form 0 f)
  read-spec-char '0' 
  pass f

Sequent = Tree Formula 

nth : Nat → Sequent → Formula 
nth k B = lookup k B ⊤*

read-bch-core : Nat → Sequent → Read Sequent
read-bch-core (suc k) B = 
  (read-spec-char '.' >> pass B) <|> 
  ( do read-spec-char ',' 
       f ← read-af k 
       read-bch-core k (add B f) )
read-bch-core 0 _ = fail "read-bch-core fail"

read-bch : Read Sequent
read-bch cs = read-bch-core (length cs) nil cs

data Proof : Set where
  rule-a : Nat → Bool → Proof → Proof
  rule-b : Nat → Proof → Proof → Proof
  rule-c : Nat → Term → Proof → Proof
  rule-d : Nat → Proof → Proof
  rule-n : Nat → Proof → Proof
  rule-s : Formula → Proof → Proof → Proof
  rule-t : Formula → Proof → Proof
  rule-x : Nat → Nat → Proof 

read-prf-core : Nat → Read Proof
read-prf-core (suc k) = 
  ( do read-spec-char 'A' 
       i ← read-nat 
       b ← read-bool 
       p ← read-prf-core k
       pass (rule-a i b p) ) <|> 
  ( do read-spec-char 'B' 
       i ← read-nat 
       p ← read-prf-core k
       q ← read-prf-core k
       pass (rule-b i p q) ) <|>
  ( do read-spec-char 'C' 
       i ← read-nat 
       t ← read-term k
       p ← read-prf-core k
       pass (rule-c i t p) ) <|>
  ( do read-spec-char 'D' 
       i ← read-nat 
       p ← read-prf-core k
       pass (rule-d i p) ) <|>
  ( do read-spec-char 'N' 
       i ← read-nat 
       p ← read-prf-core k
       pass (rule-n i p) ) <|>
  ( do read-spec-char 'S' 
       f ← read-form k 
       p ← read-prf-core k
       q ← read-prf-core k
       pass (rule-s f p q) ) <|>
  ( do read-spec-char 'T' 
       f ← read-form k 
       p ← read-prf-core k
       pass (rule-t f p) ) <|>
  ( do read-spec-char 'X' 
       i ← read-nat 
       j ← read-nat 
       pass (rule-x i j) ) 
read-prf-core 0 = fail "read-prf fail"

read-prf : Read Proof
read-prf cs = read-prf-core (length cs) cs

refl-axiom : Formula 
refl-axiom = ∀* (var 0 =* var 0)

symm-axiom : Formula 
symm-axiom = ∀* (∀* ((var 1 =* var 0) →* (var 0 =* var 1)))

trans-axiom : Formula 
trans-axiom = ∀* (∀* (∀* ((var 2 =* var 1) →* ((var 1 =* var 0) →* (var 2 =* var 0)))))

mono-args-lft : Nat → Terms 
mono-args-lft 0 = nil 
mono-args-lft (suc k) = cons (var (suc (k * 2))) (mono-args-lft k)

mono-args-rgt : Nat → Terms 
mono-args-rgt 0 = nil 
mono-args-rgt (suc k) = cons (var (k * 2)) (mono-args-rgt k)

check-mono-fun : Nat → Nat → Formula → Bool
check-mono-fun k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) =
  (c =c '=') ∧ check-mono-fun k (suc m) f
check-mono-fun k m (rel (sf (c ∷ [])) (cons (fun f0 ts0) (cons (fun f1 ts1) nil))) =
  (c =c '=') ∧ check-good-ftr (suc k) f0 ∧ (ftr-eq f0 f1 ∧ (terms-eq ts0 (mono-args-lft m) ∧ terms-eq ts1 (mono-args-rgt m)))
check-mono-fun _ _ _ = false

check-mono-rel : Nat → Nat → Formula → Bool
check-mono-rel k m (qtf false (qtf false (bct imp (rel (sf (c ∷ [])) (cons (var 1) (cons (var 0) nil))) f))) = 
  (c =c '=') ∧ check-mono-rel k (suc m) f
check-mono-rel k m (bct imp (rel r0 ts0) (rel r1 ts1)) = 
  (check-good-ftr (suc k) r0) ∧ (ftr-eq r0 r1) ∧ (terms-eq ts0 (mono-args-lft m)) ∧ (terms-eq ts1 (mono-args-rgt m))
check-mono-rel _ _ _ = false

check-vars-lt-termoid : ∀ {b} → Nat → Termoid b → Bool
check-vars-lt-termoid {true} _ nil = true
check-vars-lt-termoid {true} k (cons t ts) = 
 check-vars-lt-termoid k t ∧ check-vars-lt-termoid k ts 
check-vars-lt-termoid {false} k (var m) = m <n k
check-vars-lt-termoid {false} k (fun _ ts) = check-vars-lt-termoid k ts

check-vars-lt-form : Nat → Formula → Bool 
check-vars-lt-form k (cst _) = true
check-vars-lt-form k (not f) = check-vars-lt-form k f
check-vars-lt-form k (bct _ f g) = check-vars-lt-form k f ∧ check-vars-lt-form k g
check-vars-lt-form k (qtf _ f) = check-vars-lt-form (suc k) f
check-vars-lt-form k (rel _ ts) = check-vars-lt-termoid k ts

check-choice : Nat → Nat → Formula → Bool
check-choice k m (qtf false f) = check-choice k (suc m) f
check-choice k m (bct imp (qtf true f) g) = 
 check-good-form k f ∧ check-vars-lt-form (suc m) f ∧ 
  ( formula-eq (subst-form 0 (skm-term-asc k m) f) g ∨  
    formula-eq (subst-form 0 (skm-term-desc k m) f) g ) 
check-choice _ _ _ = false

check-pred-def : Nat → Nat → Formula → Bool
check-pred-def k a (qtf false f) = check-pred-def k (suc a) f
check-pred-def k a (bct iff (rel (nf m) ts) f) = 
  (k =n m) ∧ (check-good-form k f) ∧ (check-vars-lt-form a f) ∧ 
    (terms-eq ts (vars-asc a) ∨ terms-eq ts (vars-desc a))
check-pred-def _ _ _ = false

check-adm : Nat → Formula → Bool
check-adm k f =  
  formula-eq f (cst true) ∨
  formula-eq f (not (cst false)) ∨ 
  formula-eq f refl-axiom ∨
  formula-eq f symm-axiom ∨ 
  formula-eq f trans-axiom ∨ 
 check-mono-rel k 0 f ∨ 
 check-mono-fun k 0 f ∨ 
 check-choice k 0 f ∨ 
 check-pred-def k 0 f 

apply-a : Bool → Formula → Formula 
apply-a false  (bct and f _) =  f
apply-a true (bct and _ f) =  f
apply-a false  (not (bct or f _)) =  (not f)
apply-a true (not (bct or _ f)) =  (not f)
apply-a false  (not (bct imp f _)) =  f
apply-a true (not (bct imp _ f)) =  (not f)
apply-a false  (bct iff f g) =  (bct imp f g)
apply-a true (bct iff f g) =  (bct imp g f)
apply-a _ _ = cst true

apply-b : Bool → Formula → Formula 
apply-b false (bct or f g) = f
apply-b false (not (bct and f g)) = not f 
apply-b false (bct imp f g) = not f 
apply-b false (not (bct iff f g)) = not (bct imp f g) 
apply-b true  (bct or f g) = g
apply-b true  (not (bct and f g)) = not g
apply-b true  (bct imp f g) = g
apply-b true  (not (bct iff f g)) = not (bct imp g f)
apply-b _ _ = ⊤* 

apply-c : Term → Formula → Formula
apply-c t (qtf false f) =  (subst-form 0 t f)
apply-c t (not (qtf true f)) =  (not (subst-form 0 t f))
apply-c _ _ = ⊤*

apply-d : Nat → Formula → Formula
apply-d k (qtf true f) =  (subst-form 0 (par k) f)
apply-d k (not (qtf false f)) =  (not (subst-form 0 (par k) f))
apply-d _ _ = ⊤*

res-and : Res ⊤ → Res ⊤ → Res ⊤
res-and (cont _ cs) (cont _ _) = cont tt cs
res-and (stop s) _ = stop s
res-and (cont _ _) (stop s) = stop s

apply-n : Formula → Formula
apply-n (not (not f)) =  f
apply-n _ = ⊤*

verify : Sequent → Proof → Bool
verify Γ (rule-a i b p) = verify (add Γ (apply-a b (nth i Γ))) p
verify Γ (rule-b i p q) = 
  (verify (add Γ (apply-b false (nth i Γ))) p) ∧ 
  (verify (add Γ (apply-b true (nth i Γ))) q) 
verify Γ (rule-c i t p) = 
  check-good-term (suc (size Γ)) t ∧ 
  verify (add Γ (apply-c t (nth i Γ))) p
verify Γ (rule-d i p) = verify (add Γ (apply-d (size Γ) (nth i Γ))) p
verify Γ (rule-n i p) = verify (add Γ (apply-n (nth i Γ))) p
verify Γ (rule-s ϕ p q) = 
  check-good-form (suc (size Γ)) ϕ ∧ 
  verify (add Γ (not ϕ)) p ∧ verify (add Γ ϕ) q
verify Γ (rule-t ϕ p) =
  check-adm (size Γ) ϕ ∧ verify (add Γ ϕ) p
verify Γ (rule-x i j) = formula-eq (nth i Γ) (not (nth j Γ))
parse-verify : Chars → Chars → Bool 
parse-verify cs-bch cs-prf =
  elim-res 
    (λ B _ → elim-res (λ p _ → verify B p) (λ _ → false) (read-prf cs-prf)) 
    (λ _ → false) 
    (read-bch cs-bch)