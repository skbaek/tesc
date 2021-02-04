\documentclass{article}
\usepackage{agda}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage[verbose]{newunicodechar}
\input{unicode}
\begin{document}

\begin{code}
open import Agda.Builtin.Nat
  renaming (_<_ to _<ᵇ_)
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
  hiding (_++_ ; or ; and ; lookup ; concat) 
open import Agda.Builtin.Char
open import Data.Char
  renaming (_==_ to _=c_)
open import Data.Product
open import Data.Maybe.Base 
  renaming (_>>=_ to _o>=_)
  renaming (map to map?)
open import Agda.Builtin.Equality
open import basic
  hiding (F ; all)

data Res (A : Set) : Set where
  cont : A → Chars → Res A 
  stop : String → Res A 

Parse : Set → Set
Parse A = Chars → Res A 

infixl 20 _>>=_ 

_>>=_ : ∀ {A} {B} → Parse A → (A → Parse B) → Parse B
_>>=_ f g cs with f cs 
... | stop msg = stop msg
... | cont a cs' = g a cs'

_>>_ : ∀ {A} {B} → Parse A → Parse B → Parse B
_>>_ f g cs with f cs 
... | stop msg = stop msg
... | cont _ cs' = g cs'

infixr 20 _<|>_ 

_<|>_ : ∀ {A} → Parse A → Parse A → Parse A
_<|>_ f g cs with f cs 
... | stop _ = g cs
... | c = c

pass : {A : Set} → A → Parse A
pass x cs = cont x cs 

fail : {A : Set} → String → Parse A
fail s _ = stop s 

skip : Parse ⊤
skip = pass tt



-------- Admissability Check --------

fi<? : Nat → Functor → Bool
fi<? k (indexed m) = m <ᵇ k
fi<? _ (plain _) = true

term-lfi<? : Nat → Term → Bool
terms-lfi<? : Nat → Terms → Bool
term-lfi<? k (var _) = true
term-lfi<? k (fun f ts) = fi<? k f ∧ terms-lfi<? k ts 
terms-lfi<? k [] = true
terms-lfi<? k (t ∷ ts) = term-lfi<? k t ∧ terms-lfi<? k ts

formula-lfi<? : Nat → Formula → Bool
formula-lfi<? k (cst _) = true
formula-lfi<? k (rel r ts) = fi<? k r ∧ terms-lfi<? k ts 
formula-lfi<? k (not f) = formula-lfi<? k f 
formula-lfi<? k (qtf _ f) = formula-lfi<? k f 
formula-lfi<? k (bct _ f g) = formula-lfi<? k f ∧ formula-lfi<? k g



-------- Parsers --------

lift-parse : {A : Set} → Maybe A → Parse A 
lift-parse nothing = fail "Cannot lift nothing" 
lift-parse (just a) = pass a 

pass-if : Bool → Parse ⊤
pass-if true = pass tt
pass-if false = fail "Pass-if test failed"

parse-bool : Parse Bool
parse-bool ('0' ∷ cs) = cont false cs 
parse-bool ('1' ∷ cs) = cont true cs 
parse-bool _ = stop "Cannot parse bool (head char neither '0' nor '1')" 

parse-char : Parse Char
parse-char (c ∷ cs) = cont c cs
parse-char = fail "Cannot parse char from empty string" 

parse-chars : Parse Chars 
parse-chars ('%' ∷ cs) = cont [] cs
parse-chars (c ∷ cs) with parse-chars cs 
... | cont cs0 cs1 = cont (c ∷ cs0) cs1
... | st = st 
parse-chars = fail "parse-char fail : reached end of input string before endmarker"

parse-nat : Parse Nat
parse-nat = parse-chars >>= (lift-parse ∘ chars-to-nat)

_==c_ : Char → Char → Bool
_==c_ = primCharEquality

parse-spec-char : Char → Parse ⊤ 
parse-spec-char c0 (c1 ∷ cs) = 
  if c0 ==c c1 
    then cont tt cs 
    else stop ("char expected = " ++ fromChar c0 ++ ", char parse = " ++ fromChar c1)
parse-spec-char _ = fail "parse-spec-char fail : reached end of input string before endmarker"

parse-functor : Parse Functor
parse-functor = 
  ( do parse-spec-char '#' 
       k ← parse-nat 
       pass (indexed k) ) <|>
  ( do parse-spec-char '"' 
       s ← parse-chars 
       pass (plain s) ) 

parse-term : Nat → Parse Term
parse-terms : Nat → Parse Terms

parse-term _ ('#' ∷ cs) = ( do 
  k ← parse-nat 
  pass (var k) ) cs 
parse-term (suc k) ('$' ∷ cs) = ( do 
  f ← parse-functor 
  ts ← parse-terms k
  pass (fun f ts) ) cs 
parse-term _ = fail "parse-term fail" 
parse-terms _ ('.' ∷ cs) = cont [] cs 
parse-terms (suc k) (',' ∷ cs) = ( do 
  t ← parse-term k 
  ts ← parse-terms k
  pass (t ∷ ts) ) cs
parse-terms _ = fail "parse-terms fail" 

parse-qtf : Parse Bool
parse-qtf = 
  (parse-spec-char '!' >> pass false) <|> (parse-spec-char '?' >> pass true) 

parse-bct : Parse Bct
parse-bct = 
  (parse-spec-char '|' >> pass or) <|> 
  (parse-spec-char '&' >> pass and) <|> 
  (parse-spec-char '>' >> pass imp) <|> 
  (parse-spec-char '=' >> pass iff) 

parse-form : Nat → Parse Formula
parse-form (suc k) = 
  (parse-bool >>= λ b → pass (cst b)) <|>
  ( do parse-spec-char '$'
       f ← parse-functor 
       ts ← parse-terms k
       pass (rel f ts) ) <|>
  ( do parse-spec-char '~'
       f ← parse-form k
       pass (not f) ) <|>
  ( do b ← parse-qtf 
       f ← parse-form k
       pass (qtf b f) ) <|>
  ( do b ← parse-bct 
       f ← parse-form k
       g ← parse-form k
       pass (bct b f g) ) 
parse-form 0 = fail "parse-form fail"

parse-af : Nat → Parse Formula
parse-af k =  do
  (parse-chars >> (parse-bool >>= pass-if)) 
  f ← parse-form k 
  pass-if (formula-lfi<? 0 f)
  parse-spec-char '0' 
  pass f

Sequent = Tree Formula 

nth : Nat → Sequent → Formula 
nth k B = lookup k B ⊤*

parse-sequent-core : Nat → Sequent → Parse Sequent
parse-sequent-core (suc k) B = 
  (parse-spec-char '.' >> pass B) <|> 
  ( do parse-spec-char ',' 
       f ← parse-af k 
       parse-sequent-core k (add B f) )
parse-sequent-core 0 _ = fail "parse-sequent-core fail"

parse-sequent : Parse Sequent
parse-sequent cs = parse-sequent-core (length cs) empty cs
\end{code}

%<*proof>
\begin{code}
data Proof : Set where
  rule-a : Nat → Bool → Proof → Proof
  rule-b : Nat → Proof → Proof → Proof
  rule-c : Nat → Term → Proof → Proof
  rule-d : Nat → Proof → Proof
  rule-n : Nat → Proof → Proof
  rule-s : Formula → Proof → Proof → Proof
  rule-t : Formula → Proof → Proof
  rule-x : Nat → Nat → Proof 
\end{code}
%</proof>

\begin{code}
parse-prf-core : Nat → Parse Proof
parse-prf-core (suc k) = 
  ( do parse-spec-char 'A' 
       i ← parse-nat 
       b ← parse-bool 
       p ← parse-prf-core k
       pass (rule-a i b p) ) <|> 
  ( do parse-spec-char 'B' 
       i ← parse-nat 
       p ← parse-prf-core k
       q ← parse-prf-core k
       pass (rule-b i p q) ) <|>
  ( do parse-spec-char 'C' 
       i ← parse-nat 
       t ← parse-term k
       p ← parse-prf-core k
       pass (rule-c i t p) ) <|>
  ( do parse-spec-char 'D' 
       i ← parse-nat 
       p ← parse-prf-core k
       pass (rule-d i p) ) <|>
  ( do parse-spec-char 'N' 
       i ← parse-nat 
       p ← parse-prf-core k
       pass (rule-n i p) ) <|>
  ( do parse-spec-char 'S' 
       f ← parse-form k 
       p ← parse-prf-core k
       q ← parse-prf-core k
       pass (rule-s f p q) ) <|>
  ( do parse-spec-char 'T' 
       f ← parse-form k 
       p ← parse-prf-core k
       pass (rule-t f p) ) <|>
  ( do parse-spec-char 'X' 
       i ← parse-nat 
       j ← parse-nat 
       pass (rule-x i j) ) 
parse-prf-core 0 = fail "parse-prf fail"

parse-prf : Parse Proof
parse-prf cs = parse-prf-core (length cs) cs

refl-axiom : Formula 
refl-axiom = ∀* (var 0 =* var 0)

symm-axiom : Formula 
symm-axiom = ∀* (∀* ((var 1 =* var 0) →* (var 0 =* var 1)))

trans-axiom : Formula 
trans-axiom = ∀* (∀* (∀* ((var 2 =* var 1) →* ((var 1 =* var 0) →* (var 2 =* var 0)))))

mono-args-lft : Nat → Terms 
mono-args-lft 0 = [] 
mono-args-lft (suc k) = (var (suc (k * 2))) ∷ (mono-args-lft k)

mono-args-rgt : Nat → Terms 
mono-args-rgt 0 = [] 
mono-args-rgt (suc k) = (var (k * 2)) ∷ (mono-args-rgt k)

mono-fun? : Nat → Nat → Formula → Bool
mono-fun? k m (qtf false (qtf false (bct imp (rel (plain (c ∷ [])) ((var 1) ∷ (var 0) ∷ [])) f))) =
  (c =c '=') ∧ mono-fun? k (suc m) f
mono-fun? k m (rel (plain (c ∷ [])) ((fun f0 ts0) ∷ (fun f1 ts1) ∷ [])) =
  (c =c '=') ∧ fi<? (suc k) f0 ∧ (functor=? f0 f1 ∧ (terms=? ts0 (mono-args-lft m) ∧ terms=? ts1 (mono-args-rgt m)))
mono-fun? _ _ _ = false

mono-rel? : Nat → Nat → Formula → Bool
mono-rel? k m (qtf false (qtf false (bct imp (rel (plain (c ∷ [])) ((var 1) ∷ (var 0) ∷ [])) f))) = 
  (c =c '=') ∧ mono-rel? k (suc m) f
mono-rel? k m (bct imp (rel r0 ts0) (rel r1 ts1)) = 
  (fi<? (suc k) r0) ∧ (functor=? r0 r1) ∧ (terms=? ts0 (mono-args-lft m)) ∧ (terms=? ts1 (mono-args-rgt m))
mono-rel? _ _ _ = false
\end{code}


%<*tvlright>
\begin{code}
term-vars<? : Nat → Term → Bool
terms-vars<? : Nat → List Term → Bool
term-vars<? k (var m) = m <ᵇ k
term-vars<? k (fun _ ts) = terms-vars<? k ts
terms-vars<? _ [] = true
terms-vars<? k (t ∷ ts) = term-vars<? k t ∧ terms-vars<? k ts 
\end{code}
%</tvlright>

\begin{code}
formula-vars<? : Nat → Formula → Bool 
formula-vars<? k (cst _) = true
formula-vars<? k (not f) = formula-vars<? k f
formula-vars<? k (bct _ f g) = formula-vars<? k f ∧ formula-vars<? k g
formula-vars<? k (qtf _ f) = formula-vars<? (suc k) f
formula-vars<? k (rel _ ts) = terms-vars<? k ts

choice? : Nat → Nat → Formula → Bool
choice? k m (qtf false f) = choice? k (suc m) f
choice? k m (bct imp (qtf true f) g) = 
 formula-lfi<? k f ∧ formula-vars<? (suc m) f ∧ 
  ( formula=? (subst-form 0 (skm-term-asc k m) f) g ∨  
    formula=? (subst-form 0 (skm-term-desc k m) f) g ) 
choice? _ _ _ = false

pred-def? : Nat → Nat → Formula → Bool
pred-def? k a (qtf false f) = pred-def? k (suc a) f
pred-def? k a (bct iff (rel (indexed m) ts) f) = 
  (k =n m) ∧ (formula-lfi<? k f) ∧ (formula-vars<? a f) ∧ 
    (terms=? ts (vars-asc a) ∨ terms=? ts (vars-desc a))
pred-def? _ _ _ = false

adm? : Nat → Formula → Bool
adm? k f =  
  formula=? f (cst true) ∨
  formula=? f (not (cst false)) ∨ 
  formula=? f refl-axiom ∨
  formula=? f symm-axiom ∨ 
  formula=? f trans-axiom ∨ 
 mono-rel? k 0 f ∨ 
 mono-fun? k 0 f ∨ 
 choice? k 0 f ∨ 
 pred-def? k 0 f 

analyze-a : Bool → Formula → Formula 
analyze-a false  (bct and f _) =  f
analyze-a true (bct and _ f) =  f
analyze-a false  (not (bct or f _)) = (not f)
analyze-a true (not (bct or _ f)) = (not f)
analyze-a false  (not (bct imp f _)) = f
analyze-a true (not (bct imp _ f)) = (not f)
analyze-a false  (bct iff f g) = (bct imp f g)
analyze-a true (bct iff f g) = (bct imp g f)
analyze-a _ _ = cst true

analyze-b : Bool → Formula → Formula 
analyze-b false (bct or f g) = f
analyze-b false (not (bct and f g)) = not f 
analyze-b false (bct imp f g) = not f 
analyze-b false (not (bct iff f g)) = not (bct imp f g) 
analyze-b true  (bct or f g) = g
analyze-b true  (not (bct and f g)) = not g
analyze-b true  (bct imp f g) = g
analyze-b true  (not (bct iff f g)) = not (bct imp g f)
analyze-b _ _ = ⊤* 

analyze-c : Term → Formula → Formula
analyze-c t (qtf false f) =  (subst-form 0 t f)
analyze-c t (not (qtf true f)) =  (not (subst-form 0 t f))
analyze-c _ _ = ⊤*

analyze-d : Nat → Formula → Formula
analyze-d k (qtf true f) =  (subst-form 0 (par k) f)
analyze-d k (not (qtf false f)) =  (not (subst-form 0 (par k) f))
analyze-d _ _ = ⊤*

analyze-n : Formula → Formula
analyze-n (not (not f)) =  f
analyze-n _ = ⊤*
\end{code}

%<*verify-c>
\begin{code}
verify : Sequent → Proof → Bool
verify Γ (rule-c i t p) = 
  term-lfi<? (suc (size Γ)) t ∧ 
  verify (add Γ (analyze-c t (nth i Γ))) p
\end{code}
%</verify-c>

\begin{code}
verify Γ (rule-a i b p) = verify (add Γ (analyze-a b (nth i Γ))) p
verify Γ (rule-b i p q) = 
  (verify (add Γ (analyze-b false (nth i Γ))) p) ∧ 
  (verify (add Γ (analyze-b true (nth i Γ))) q) 
verify Γ (rule-d i p) = verify (add Γ (analyze-d (size Γ) (nth i Γ))) p
verify Γ (rule-n i p) = verify (add Γ (analyze-n (nth i Γ))) p
verify Γ (rule-s ϕ p q) = 
  formula-lfi<? (suc (size Γ)) ϕ ∧ 
  verify (add Γ (not ϕ)) p ∧ verify (add Γ ϕ) q
verify Γ (rule-t ϕ p) =
  adm? (size Γ) ϕ ∧ verify (add Γ ϕ) p
verify Γ (rule-x i j) = formula=? (nth i Γ) (not (nth j Γ))

elim-res : {A B : Set} → (A → Chars → B) → (String → B) → (Res A) → B
elim-res f g (cont a cs) = f a cs
elim-res f g (stop s) = g s

parse-verify : Chars → Chars → Bool 
parse-verify cs-bch cs-prf =
  elim-res 
    (λ B _ → elim-res (λ p _ → verify B p) (λ _ → false) (parse-prf cs-prf)) 
    (λ _ → false) 
    (parse-sequent cs-bch)
\end{code}