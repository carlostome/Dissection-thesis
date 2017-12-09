%include proposal.fmt
%include polycode.fmt

\section{Introduction}\label{sec:Introduction}

The functional programming paradigm advocates for a style of programming based
on higher-order functions over inductively defined datatypes. A fold is the
prototypical example of such function. Using a fold for computation comes at a
price. The definition of a fold is not tail recursive which means that the size
of the stack during execution grows proportionally to the size of the input.
McBride has proposed a method,
\emph{dissection}\cite{McBride:2008:CLM:1328438.1328474}, to allow the
transformation of a fold into its tail-recursive counterpart. However, it is not
clear that the resulting function is correct neither that it terminates.

\subsection{Description of the problem}
\label{subsec:problem}

Folds are a well understood formalism in the toolbox of the functional
programmer. 
Many calculae have beare a common recurring combinator in the functional programmer toolbox.
- folds are good
- well studied
- structure code
- calculae
- proof principle and computation rule

Example folds for lists:

\begin{code}
  foldr f z []     = z
  foldr f z (x:xs) = f x (foldr f z xs)
\end{code}

Assuming we have a
\begin{code}
foldr (+) 0 [1..1000000] ~>
1 + (foldr (+) 0 [2..1000000]) ~>
1 + (2 + (foldr (+) 0 [3..1000000])) ~>
1 + (2 + (3 + (foldr (+) 0 [4..1000000]))) ~>
1 + (2 + (3 + (4 + (foldr (+) 0 [5..1000000])))) ~>

\end{code}

- however let us illustrate how foldr evaluates

- the internal stack of the execution machine grows proportionally to the size
of the input. Bad

- For lists we can do better because of the linear structure it is easily to
recover the foldl from foldr

How would we do this for trees?
two functions
However for non linear structures it is not that simple. MCBride has a method
that works for polynomial fixed points. Or he claims so!

For example huttons razor. What is the problem? It does not perform structural
recursion over its arguments we can try to encode it in Agda but doesn't pass
the termination checker,

\subsection{Research question}

The master thesis that this documents serves as a proposal aims to investigate
whether it would be possible to formalize MCBride's notion of dissection for
transforming a fold into a tail-recursive operator that is extensionally
equivalent. To be more specific, we aim to provide a machine checked proof of it
using the proof assistant \Agda.

In order to do so, we need to address the following specific problems.

  \medskip

  \noindent
  \textbf{Termination} The transformation requires to make explicit the stack
  underlying the computation. During the execution, the stack holds the parts
  of the branching structure of the datatype that will be further processed.
  By using a simply typed stack all information about the relation between
  what is in the stack and what is being proccessed is lost and the recursion
  is not anymore on arguments that are structurally smaller.

  \medskip

  \noindent
  \textbf{Correctness} Once termination is proved, the next step aims to prove
  that the transformation is correct.  By correct it is  understood that both
  the fold and the its tail-recursive counterpart are extensionally equivalent,
  i.e. for any input both functions compute the same result.

  \medskip

  \noindent
  \textbf{Generalization} McBride proposes a method for calculating the type of
  the stack from the definition of any type that can be expressed as a
  polynomial functor. We aim to formalize his notion of \emph{dissection} of a
  datatype and show how termination and correctness can be generalized to deal
  with types that can be expressed as polynomial functors.

\subsection{Proposal}

  % This document is organized as follows, i
