\documentclass{article}
\usepackage{agda}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage[verbose]{newunicodechar}
\input{unicode}
\begin{document}

\begin{code}
module other where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
  using (Nat)
  renaming (_<_ to _<ᵇ_)
open import Data.List 
  using (List ; all)
open import basic
  using (Term ; var ; fun)

{-# NON_TERMINATING #-}
\end{code}

%<*tvlwrong>
\begin{code}
term-vars<? : Nat → Term → Bool
term-vars<? k (var m) = m <ᵇ k
term-vars<? k (fun _ ts) = all (term-vars<? k) ts
\end{code}
%</tvlwrong>

\end{document}
