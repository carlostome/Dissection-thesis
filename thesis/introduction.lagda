%include introduction.fmt

\chapter{Introduction}\label{sec:Introduction}
\label{chap:intro}

Folds, or \emph{catamorphisms}, are a pervasive programming pattern. Folds
generalize many simple traversals over algebraic data
types~\citep{meijer1991functional}. Functions
implemented by means of a fold are both compositional and structurally
recursive. The fold associated with a datatype, however, is not a tail-recursive
function.

We start this chapter with a detailed description of the problem that motivates
the research conducted within this master thesis (\Cref{sec:intro:descr}), and
subsequently, we formulate the concrete research questions
(\Cref{sec:intro:research}). Lastly, in \cref{sec:intro:org} we outline the
organization of the rest of this document.

\section{Description of the problem}\label{subsec:problem}
\label{sec:intro:descr}

The |foldr| function is one of the first higher-order functions that any
functional programmer learns~\citep{hutton2016programming}. Many simple functions over lists such as |map|,
|reverse|, |take|, |sum|, and more can be expressed in terms of
|foldr|.  However, if not used carefully, |foldr| may cause a \emph{well-typed
program go wrong} by dynamically failing with a stack overflow. In order to
understand the problem, let us review the definition of |foldr|:\footnote{Code
snippets within this thesis are written in the dependently typed programming
language \Agda~\citep{norell}}
%
\begin{code}
  foldr : (a -> b -> b) -> b -> List a -> b
  foldr f e []         = e
  foldr f e (x :: xs)  = f x (foldr f e xs)
\end{code}
%
In the second clause of the definition, the parameter function |f| cannot
reduce further before the result of the recursive call on the argument |xs| is
available. This is a problem of both strict languages and non-strict languages
with strict functions. 

If we think about it in terms of the execution of a stack machine, before the
control flow is passed to the recursive call, a new frame has to be allocated on
the top of the stack to resume with the reduction of |f|.  Only a finite number
of frames may be ever pushed on the stack before it reaches its limit.
Performing a few steps of the evaluation of adding a very big list of numbers
illustrates the issue:
%
\begin{code}
foldr  plusOp 0 [ 1..1000000 ] 
       ~> 1 + (foldr plusOp 0 [ 2..1000000 ]) 
       ~> 1 + (2 + (foldr plusOp 0 [ 3..1000000 ])) 
       ~> 1 + (2 + (3 + (foldr plusOp 0 [ 4..1000000 ]))) 
       ~> 1 + (2 + (3 + (4 + (foldr plusOp 0 [ 5..1000000 ])))) 
       ~> ...
\end{code}
%
At each step of the reduction, denoted by |~>|, the size of the expression being
evaluated reflects the size of the underlying machine's stack. Before any
addition can actually reduce, the function |foldr| has to reach the end of the
list; during the evaluation, |foldr| needs to allocate every intermediate
application of |plusOp| on the stack. The linear dependency between the size of the
input and the size of the stack, can potentially lead to a stack overflow on
large inputs.

To solve this problem, we can rewrite the function to be
\emph{tail-recursive}. The definition of a tail-recursive function does not
allow for another function to post process the result of the recursive calls.
In each clause, either a value is returned or a recursive call is the final action
to be performed. Modern compilers typically map tail-recursive functions to
machine code that runs in constant stack space~\citep{Steele:1977:DLP:800179.810196}.

In the case of the function |foldr|, a possible implementation of an equivalent
tail-recursive function would be a left fold, |foldl|. Its definition is as
follows:
%
\begin{code}
  foldl : (a -> b -> b) -> b -> List a -> b
  foldl f e []         = e
  foldl f e (x :: xs)  = foldl f (f x e) xs
\end{code}
%
Using |foldl|, the addition of the previous list of numbers runs in constant
stack space:
%
\begin{code}
foldl  plusOp 0 [ 1..1000000 ] 
       ~> foldl plusOp (1 + 0) [ 2..1000000 ]
       ~> foldl plusOp 1 [ 2..1000000 ] 
       ~> foldl plusOp (2 + 1) [ 3..1000000 ]
       ~> foldl plusOp 3 [ 3..1000000 ]
       ~> foldl plusOp (3 + 3) [ 4..1000000 ]
       ~> foldl plusOp 6 [ 4..1000000 ] 
       ~> ...
\end{code}

However, for inductive datatypes with constructors that have more than one
recursive subtree, recovering a tail-recursive fold from the regular fold is not
as straightforward.

\paragraph{Folds for binary trees}

As an example of a datatype with more than one recursive subtree, we consider
the type of binary trees with natural numbers in the leaves:
%
\begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
\end{code}

We can write a simple evaluator, mapping expressions to natural numbers as
follows:
%
\begin{code}
  eval : Expr -> Nat
  eval (Val n)      = n
  eval (Add e1 e2)  = eval e1 + eval e2
\end{code}
%
In the case for |Add e1 e2|, the |eval| function makes two recursive calls and
sums their results. Such a function can be implemented using a fold, passing the
addition and identity functions as the argument algebra. The algebra is the pair
of functions that assigns semantics to the constructors of |Expr|:
%
\begin{code}
  foldExpr : (Nat -> a) -> (a -> a -> a) -> Expr -> a
  foldExpr alg1 alg2 (Val n)      = alg1 n
  foldExpr alg1 alg2 (Add e1 e2)  = alg2 (foldExpr alg1 alg2 e1) (foldExpr alg1 alg2 e2)

  eval : Expr -> Nat
  eval = foldExpr id plusOp
\end{code}
%
Unfortunately, the definition of |eval| suffers from the same shortcomings as
the |List| function |foldr|. The operator |plusOp| needs both of its parameters
to be fully evaluated before it can reduce further, thus the stack used during
execution grows \emph{again} linearly with the size of the input.

To address the problem, we can \emph{manually} rewrite the evaluator to be
\emph{tail-recursive}. To write such a tail-recursive function, we need to 
introduce an explicit stack storing both intermediate results and the subtrees 
that have not yet been evaluated:
%
\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}

We can define a tail-recursive evaluation function by means of a pair of
mutually recursive functions, |load| and |unload|. The |load| function traverses
the expressions, pushing subtrees on the stack; the |unload| function unloads
the stack, while accumulating a (partial) result:
%
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload v   Top             = v
    unload v   (Right v' stk)  = unloadN (v' + v) stk
    unload v   (Left e stk)    = loadN e (Right v stk)
\end{code}

We can now define a tail-recursive version of |eval| by
calling |load| with an initially empty stack:
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = load e Top
\end{code}

Implementing this tail-recursive evaluator comes at a price: \Agda's termination
checker flags the |load| and |unload| functions as potentially non-terminating
by highlighting them \nonterm{orange}. Indeed, in the very last clause of the
|unload| function a recursive call is made to arguments that are not
syntactically smaller. Furthermore, it is not clear at all whether the
tail-recursive evaluator, |tail-rec-eval|, produces the same result as our original |eval|
function.

\section{Research questions}
\label{sec:intro:research}

As previously shown, it is not obvious how to write a \emph{provably}
terminating and correct tail-recursive evaluator for the type of binary trees.
A necessary prerequisite to show correctness, is to convince \Agda's termination
checker that the tail-recursive evaluator terminates. Thus, we are ready to
spell the research questions that this master thesis is set out to answer:

\begin{enumerate}
  \item \textbf{Termination} \Agda's termination checker cannot verify that the
    functions |load| and |unload|, as previously defined, terminate for every
    possible input. How can we demonstrate that the functions terminate, so
    that as a corollary the tail-recursive evaluator terminates?

  \item \textbf{Correctness} In the case the tail-recursive evaluator
    terminates, it is correct? By correct it is understood that both the
    evaluation function, |eval|, and  its tail-recursive counterpart,
    |tail-rec-eval|, are equivalent: for any input both functions
    compute the same result.

  \item  \textbf{Generalization to the \emph{regular} universe} McBride proposes
    a method, \emph{dissection}~\citeyearpar{McBride:2008:CLM:1328438.1328474},
    for calculating the type of the \emph{stack} from the definition of any type
    that can be generically expressed in the \emph{regular} universe. Can we
    generalize the results of \textbf{termination} and \textbf{correctness} from
    |Expr| to the generic case through \emph{dissection}?
\end{enumerate}

We answer questions one and two in \cref{chap:expression}, where we show how to
\emph{manually} write a tail-recursive evaluator for the type of |Expr|. We
subsequently prove the evaluator to be both terminating and correct with respect
to the fold.

In \cref{chap:generic}, we answer the third research question. Particularly, we
generalize the result from \cref{chap:expression} and develop a terminating
tail-recursive evaluator that works for any algebra over any regular datatype.
Additionally, we prove the evaluator to be correct with regard to the
fold associated with the datatype.

\section{Organization}
\label{sec:intro:org}

  This master thesis is divided in four chapters.
  
  We start in
  \cref{chap:background} giving the reader a broader perspective on folds in
  programming languages to justify the importance of our our work.  Furthermore,
  we revisit the available literature on techniques to assist the termination
  checker to accept functions that are not defined by strictly structural
  recursion. We end the \namecref{chap:background} with an introduction to
  generic programming in \Agda~using the \emph{regular} universe, which forms
  the basis of our generic tail-recursive evaluator.

  \Cref{chap:expression,chap:generic} contain the main contributions of this
  master thesis: a provably terminating and correct tail-recursive function
  equivalent to the fold over |Expr|, and its generalization to the regular
  universe.

  We conclude this document, in \cref{chap:conclusion}, with a few remarks about
  the work presented here and discuss possible future directions to pursue.

\paragraph{Style}

  Before dwelling into the content, we have to remark a few conventions that
  this document follows. The purpose of the code snippets present in this thesis
  is to guide the reader through the ideas of our construction, thus in many
  cases only the type signature of the relevant functions/theorems/datatypes is
  given, and the body is omitted altogether. All code snippets use \Agda~syntax,
  although not all of them typecheck directly. In the type signatures, any
  mentioned variable of type |Set| is taken as implicitly universally
  quantified. To differentiate between functions and theorems (in
  dependent type theory they are the same) we choose to prepend the type
  signatures of the latter with a explicit |forall| quantifier. The full \Agda~
  formalization is freely available online in:
  \medskip
  \begin{center}
  \url{https://github.com/carlostome/Dissection-thesis}
  \end{center}
