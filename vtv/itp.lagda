\documentclass{article}
\usepackage{agda}
\begin{document}

\begin{code}
module itp where

open import Data.Bool
  using (Bool)
\end{code}

%<*foo>
\begin{code}
VA : Set 
VA = Bool → Bool
\end{code}
%</foo>


\end{document}