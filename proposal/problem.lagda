%include proposal.fmt
%include lhs2TeX.fmt

\section{Introduction}\label{sec:Introduction}

The functional programming paradigm advocates for a style of programming based
on higher-order functions over inductively defined datatypes. A fold is the
prototypical example of such a function, but its use for computation comes
at a price. The definition of a fold is not tail recursive which means that the
size of the stack during execution grows proportionally to the size of the
input.  McBride has proposed a method,
\emph{dissection}\cite{McBride:2008:CLM:1328438.1328474}, to allow the
transformation of a fold into its tail-recursive counterpart. However, it is not
clear why the resulting function terminates, neither if it is correct.

\subsection{Description of the problem}\label{subsec:problem}

|foldr| for the list type is one of the first functions that any functional
programmer learns about. Many sensible functions over lists such as |map|,
|reverse|, |take|, |sum|, |and| ... can be expressed in terms of |foldr|.
However, if not used carefully, |foldr| may cause a well intentioned program to
never deliver its result because of a stack overflow. In order to understand the
problem let us review its definition using notation from our favorite functional
programming language, Haskell.

\begin{code}
  foldr :: (a -> b -> b) -> b -> [a] -> b
  foldr f z []     = z
  foldr f z (x:xs) = f x (foldr f z xs)
\end{code}

In the second clause of the definition, the recursive call to |foldr| does not
occur in last position. |f| needs to wait until a result has been computed for
the rest of the list to follow through. In terms of execution on a stack
machine, this means that a frame is allocated before passing the control to the
recursive call for later processing. Only a finite number of frames may be
pushed on the stack before it reaches its limit. Performing a few steps of the
evaluation of adding a very big list of numbers evidences the issue.

\begin{code}
foldr (+) 0 [1..1000000] ~>
1 + (foldr (+) 0 [2..1000000]) ~>
1 + (2 + (foldr (+) 0 [3..1000000])) ~>
1 + (2 + (3 + (foldr (+) 0 [4..1000000]))) ~>
1 + (2 + (3 + (4 + (foldr (+) 0 [5..1000000])))) ~>
...
\end{code}

At each step, the size of the expression reflects faithfully the size of the
underlying stack. Using a tail recursive function --where the last call is to
the function itself--, an optimizing compiler can directly pass the control to
the recursive call without needing to allocate a stack frame. Without
post processing there is no need to save intermediate results.  For the list
type, the problem can be solved by using a left fold\footnote{Imposing further
restrictions on the function |f : (a -> b -> b)|} (|foldl|). However, for
non-linear structures, is not as straightforward to recover a tail-recursive
function that computes the same folds.

As an example let us consider the type of arithmetic expressions or binary trees
with integers in the leaves\footnote{The folklore names it Hutton's razor} (from
now on we will use \Agda~notation).

\InsertCode{Proposal/Expr.tex}{Expr}

\InsertCode{Proposal/Expr.tex}{Eval-tr}

Values of \AD{Expr} can be evaluated by using a \AF{eval} function that performs
structural recursion on the input. The \AI{Add} constructor represents addition
\AF{+}.

\InsertCode{Proposal/Expr.tex}{Eval}

\AF{eval} is nothing more than a fold over \AD{Expr} where the function that combines
results from the subtrees is fixed. \AF{eval} is again not tail recursive because
\AF{+} needs the results\footnote{For non-strict functions this may not be true} of
both subtrees before the evaluation can proceed.

To transform \AF{eval} into a tail-recursive version that computes the "same"
result we make the execution stack (the one that holds intermediate
computations) explicit and write a function that is tail recursive over it. The
type of the stack reflects the state of evaluation at each step. The idea is
that for computing the value of \mbox{\AD{Add}\AS{}\AB{e1}\AS{}\AB{e2}} we can
store \AB{e2} onto the stack while we evaluate \AB{e1}. When \AB{e1} yields a
result we can pop up \AB{e2} to process it while storing the result of \AB{e1}
onto the stack.  This can be accomplished by defining a type for the stack as
follows.

\InsertCode{Proposal/Expr.tex}{Stack}

A pair of mutually recursive functions, \AF{load} and \AF{unload}, that perform
the evaluation. The former searches for the leftmost subtree on the expression
while the latter performs the evaluation once we are in a right subtree.

\InsertCode{Proposal/Expr.tex}{load-unload}
\colored

Then what is the problem? The definition of \AF{load}/\AF{unload} is not
accepted by \Agda's termination checker\footnote{With \nonterm{this color}
\Agda~warns that the termination checker fails.}. In the definition the
recursive calls are not performed over values that are evidently structurally
smaller than the input.  Moreover, without proof we have no evidence that the
result computed by the function is the same as the original \AF{eval} for any
possible input.

\subsection{Research objective}

The master thesis that this documents serves as a proposal aims to investigate
whether it would be possible to use MCBride's notion of dissection for
transforming a fold into a tail-recursive function that is extensionally
equivalent. To be more specific, we aim to provide a machine checked proof of it
using the proof assistant \Agda.

In order to do so, we need to address the following specific problems.

  \medskip

  \noindent
  \textbf{Termination} As explained, the transformation requires to make
  explicit the stack underlying the computation. During the execution, the stack
  holds the parts of the branching structure of the datatype that will be
  further processed.  By using a simply typed stack all information about the
  relation between what is in the stack and what is being processed is lost and
  recursive calls done on subtrees on the stack are not --evidently-- structurally
  smaller than the original input.

  \medskip

  \noindent
  \textbf{Correctness} Once termination is proved, the next step aims to prove
  that the transformation is correct. By correct it is understood that both
  the fold and the its tail-recursive counterpart are extensionally equivalent,
  i.e. for any input both functions compute the same result.

  \medskip

  \noindent
  \textbf{Generalization to Regular trees} McBride proposes a method for
  calculating the type of the stack from the definition of any type that can be
  expressed as a \emph{Regular} tree functor. We aim to formalize his notion of
  \emph{dissection} of a datatype and show how termination and correctness can
  be generalized to deal with types that can be expressed as \emph{Regular} tree
  types.

\subsection{Proposal}

  The rest of the document is organized as follows. In \cref{sec:termination} we
  explore common techniques used in type theory to prove that a function
  terminates (can be defined) even though is not defined by structural induction
  over its input. \cref{sec:generic} explores how generic programming can be
  exploited to define a tail-recursive fold through the notion of dissection.
  \cref{sec:prototype} describes the preliminar work done during the proposal
  phase, showing that it is possible to prove termination through \emph{well
  founded} recursion of a tail recursive traversal --left to right-- over binary
  trees.
