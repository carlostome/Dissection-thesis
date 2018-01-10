
%include polycode.fmt
%include proposal.fmt

%{
%format Expr  = "\AD{Expr}"
%format Val   = "\AD{Val}"
%format Add   = "\AD{Add}"
%format eval  = "\AF{eval}"
%format +     = "\AF{+}"
%format Stack = "\AD{Stack}"
%format Top   = "\AD{Top}"
%format Left  = "\AD{Left}"
%format Right = "\AD{Right}"
%format load  = "\AF{load}"
%format unload  = "\AF{unload}"
%format foldr = "\AF{foldr}"
%format foldl = "\AF{foldl}"

%format plusOp = "\AF{\_+\_}"

%format n     = "\AB{n}"
%format e1    = "\AB{\ensuremath{e_1}}"
%format e2    = "\AB{\ensuremath{e_2}}"


\section{Introduction}\label{sec:Introduction}

The functional programming paradigm advocates for a style of programming based
on higher-order functions over inductively defined datatypes. A fold, which
captures their common pattern of recursion, is the prototypical example of such a
function. However, its use for computation comes at a price. The definition of a
fold is not tail recursive which means that the size of the stack during
execution grows proportionally to the size of the input.  McBride has proposed a
method, \emph{dissection}\cite{McBride:2008:CLM:1328438.1328474}, to transform a
fold into its tail-recursive counterpart. Nevertheless, it is not clear why the
resulting function terminates, nor it is clear that the transformation preserves
the fold's semantics.

\subsection{Description of the problem}\label{subsec:problem}

The |foldr| function is one of the first higher-order functions that any
functional programmer learns. Many simple functions over lists such as |map|,
|reverse|, |take|, |sum|, |and| ... can be expressed in terms of |foldr|.
However, if not used carefully, |foldr| may cause a program to fail dynamically
with a stack overflow. To understand the problem let us review its definition.
From now on, all code snippets will use \Agda~notation.

\begin{code}
  foldr : (a -> b -> b) -> b -> List a -> b
  foldr f z []         = z
  foldr f z (x :: xs)  = f x (foldr f z xs)
\end{code}

In the second clause of the definition, the parameter function |f| needs to wait
until a result has been computed for the recursive call before it can reduce
further. In terms of execution on a stack machine, this means that a frame has
to be allocated before passing the control to the recursive call for later
processing.  Only a finite number of frames may be pushed on the stack before it
reaches its limit. Performing a few steps of the evaluation of adding a very big
list of numbers illustrates the issue.

%{
%format ~> = "\leadsto"
\begin{code}
foldr (+) 0 [1..1000000] ~>
1 + (foldr (+) 0 [2..1000000]) ~>
1 + (2 + (foldr (+) 0 [3..1000000])) ~>
1 + (2 + (3 + (foldr (+) 0 [4..1000000]))) ~>
1 + (2 + (3 + (4 + (foldr (+) 0 [5..1000000])))) ~>
...
\end{code}
%}

At each step, the size of the expression matches the size of the underlying
stack. Using a tail recursive function --where the result of the recursive
calls are not used by another function to compute the result-- an optimizing
compiler can directly pass the control to the recursive call without needing to
allocate a stack frame. Avoiding post processing means there is no need to save
intermediate results.  For the list type, the problem can be solved by using a
left fold\footnote{Imposing further restrictions on the function |f : (a -> b ->
b)| (see \cite{Hutton93atutorial}).} (|foldl|). However, for non-linear
structures, is not as straightforward to recover a tail recursive function that
evaluates to the same result.

As an example let us consider the type of arithmetic expressions or binary trees
with integers in the leaves\footnote{The folklore names it Hutton's razor}.

\begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
\end{code}

Values of |Expr| can be evaluated by using a |eval| function that performs
structural recursion on the input. The |Add| constructor represents addition
|+|.

\begin{code}
  eval : Expr -> Nat
  eval (Val n)      = n
  eval (Add e1 e2)  = eval e1 + eval e2
\end{code}

The function |eval| is nothing more than a fold over |Expr| where the function
that combines results from the subtrees is fixed. The |eval| function is not
tail recursive because the |plusOp| operator needs the result of both subtrees
before the evaluation can proceed.

To transform |eval| into a tail-recursive version that computes the "same" final
result we make the execution stack, holding intermediate computations, explicit
. The type of the stack reflects the state of evaluation at each step. The idea
is that for computing the value of |Add e1 e2| we can store |e2| onto the stack
while we evaluate |e1|. When |e1| yields a result we can pop up |e2| to process
it while storing the result of |e1| onto the stack.  This can be accomplished by
defining a type for the stack as follows.

\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}

A pair of mutually recursive functions, \AF{load} and \AF{unload}, perform the
evaluation. The former searches for the leftmost subtree on the expression while
the latter performs the evaluation once we are in a right subtree. Both
functions are tail recursive.

%{
%format loadN   = "\nonterm{" load "}"
%format unloadN = "\nonterm{" unload "}"
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 ( Left e2 stk )

    unloadN : Nat -> Stack -> Nat
    unload v Top             = v
    unload v (Right v' stk)  = unloadN (v' + v) stk
    unload v (Left r stk)    = loadN r (Right v stk)

  eval : Expr → ℕ
  eval e = load e Top
\end{code}
%}


Then what is the problem? The definition of \AF{load}/\AF{unload} is not
accepted by \Agda's termination checker\footnote{With \nonterm{this color}
\Agda~warns that the termination checker fails.}. In the definition, the
recursive calls are not performed over values that are evidently structurally
smaller than the input.  Moreover, without proof we have no evidence that the
result computed by the function is the same as the original \AF{eval} for every
input.

\subsection{Research objective}

The master thesis aims to investigate whether it would be possible to use
McBride's notion of dissection to transform a fold into an extensionally
equivalent tail-recursive function. To be more specific, we aim to
provide a machine checked proof of this equality using the proof assistant \Agda.

In order to do so, we need to address the following specific problems.

  \medskip

  \noindent
  \textbf{Termination} As explained, the transformation requires to make
  the stack underlying the computation explicit. During the execution, the stack
  holds the parts of the branching structure of the datatype that will be
  further processed.  By using a simply typed stack all information about the
  relation between what is in the stack and what is being processed is lost and
  recursive calls done on subtrees on the stack are not -- obvious -- structurally
  smaller than the original input.

  \medskip

  \noindent
  \textbf{Correctness} Once termination is proved, the next step aims to prove
  that the transformation is correct. By correct it is understood that both
  the fold and the its tail-recursive transformation are extensionally equivalent,
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

  The rest of the document is organized as follows. In \Cref{sec:termination} we
  explore common techniques used in type theory to prove that a function
  terminates even though is not defined by structural induction
  over its input. \Cref{sec:generic} explores how generic programming can be
  exploited to define a tail-recursive fold through the notion of dissection.
  \Cref{sec:prototype} describes the preliminar work done during the proposal
  phase, showing that it is possible to prove termination through \emph{well
  founded} recursion of a tail recursive traversal over binary
  trees.
%}

