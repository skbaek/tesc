open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate plus-commute : (a b : Nat) → a + b ≡ b + a
postulate P : Nat → Set

thm : (a b : Nat) → P (a + b) → P (b + a)
thm a b t with a + b | plus-commute a b
... | _ | refl = t