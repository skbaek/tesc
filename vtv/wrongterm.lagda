\documentclass{article}
\usepackage{agda}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage[verbose]{newunicodechar}
\input{unicode}
\begin{document}

\begin{code}
module wrongterm where

open import Agda.Builtin.Nat
  using (Nat)
open import Data.List 
  using (List)
\end{code}

%<*wrongterm>
\begin{code}
data Term : Set where 
  var : Nat → Term 
  fun : Functor → List Term → Term 
\end{code}
%</wrongterm>