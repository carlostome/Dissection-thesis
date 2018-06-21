%include introduction.fmt

\chapter{Introduction}\label{sec:Introduction}
\label{chap:intro}

The functional programming paradigm advocates a style of programming based
on higher-order functions over inductively defined datatypes. A fold, which
captures their common pattern of recursion, is the prototypical example of such a
function. However, its use for computation comes at a price. The definition of a
fold is not tail-recursive which means that the size of the stack during
execution grows proportionally to the size of the input.  McBride has proposed a
method called \emph{dissection}\cite{McBride:2008:CLM:1328438.1328474}, to transform a
fold into its tail-recursive counterpart. Nevertheless, it is not clear why the
resulting function terminates, nor it is clear that the transformation preserves
the fold's semantics.

\section{Description of the problem}\label{subsec:problem}
\label{sec:intro:descr}

The |foldr| function is one of the first higher-order functions that any
functional programmer learns. Many simple functions over lists such as |map|,
|reverse|, |take|, |sum|, and many more can be expressed in terms of
|foldr|.  However, if not used carefully, |foldr| may cause a \emph{well-typed
program go wrong} by dynamically failing with a stack overflow. In order to
understand the problem, let us review the definition of |foldr|\footnote{All
code snippets within this thesis use \Agda~notation.}:
%
\begin{code}
  foldr : (a -> b -> b) -> b -> List a -> b
  foldr f e []         = e
  foldr f e (x :: xs)  = f x (foldr f e xs)
\end{code}
%
In the second clause of the definition, the parameter function |f| can not
reduce further before the result of the recursive call on the argument |xs| is
available. If we think about it in terms of the execution of a stack machine,
before the control flow is passed to the recursive call, a new frame has to be
allocated on the top of the stack to resume with the reduction of |f|.
Only a finite number of frames may be ever pushed on the stack
before it reaches its limit. Performing a few steps of the evaluation of adding
a very big list of numbers illustrates the issue:
%
\begin{code}
foldr  (+) 0 [1..1000000] 
       ~> 1 + (foldr (+) 0 [2..1000000]) 
       ~> 1 + (2 + (foldr (+) 0 [3..1000000])) 
       ~> 1 + (2 + (3 + (foldr (+) 0 [4..1000000]))) 
       ~> 1 + (2 + (3 + (4 + (foldr (+) 0 [5..1000000])))) 
       ~> ...
\end{code}
%
At each step of the reduction, denoted by |~>|, the size of the expression being
evaluated reflects the size of the underlying machine's stack. Before any addition 
can actually reduce, the function |foldr| has to reach the end of the list, thus 
for every intermediate reduction, the function is allocating a partially applied |plusOp|
on the stack. The linear dependency between the size of the input and the size
of the stack, can potentially lead to a stack overflow on large inputs.

To solve this problem, we can rewrite the function to be
\emph{tail-recursive}. The definition of a tail-recursive function does not
allow for another function to post process the result of the recursive calls.
In each clause, either a value is returned or a recursive call is the final action
to be performed. Modern compilers typically map tail-recursive functions to
machine code that runs in constant memory.

In the case of the function |foldr|, a possible implementation of an equivalent
tail-recursive function would be a left fold, |foldl|\footnote{Imposing further
restrictions on the function |f : (a -> b -> b)| (see
\cite{Hutton93atutorial}).}. However, for inductive datatypes with constructors
that have more than one recursive occurrence, such as the type of binary trees,
recovering a tail-recursive fold from the regular fold is not as straightforward.

In the following sections, we present a concrete example of a datatype with a
tree-like branching structure and define its associated fold. Moreover, we show
how to define a tail-recursive function that we claim, without proof, equivalent 
to the fold. By doing so, we identify the key goal of the present master thesis,
and subsequently formulate the research questions that it answers. Finally, in
\Cref{sec:intro:org}, we explain how the rest of the document is organized. 

\paragraph{Folds for Binary Trees}

As an example of a tree-like branching datatype we consider the type of
binary trees with natural numbers in the leaves:
\begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
\end{code}
We can write a simple evaluator, mapping expressions to natural numbers as
follows:
\begin{code}
  eval : Expr -> Nat
  eval (Val n)      = n
  eval (Add e1 e2)  = eval e1 + eval e2
\end{code}
%
In the case for |Add e1 e2|, the |eval| function makes two recursive
calls and sums their results. Such a function can be implemented using a
fold, passing the addition and identity functions as the argument
algebra.
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
\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}
We can define a tail-recursive evaluation function by means of a pair of
mutually recursive functions, |load| and |unload|. The |load| function traverses
the expressions, pushing subtrees on the stack; the |unload| function unloads
the stack, while accumulating a (partial) result.
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload v   Top             = v
    unload v   (Right v' stk)  = unloadN (v' + v) stk
    unload v   (Left r stk)    = loadN r (Right v stk)
\end{code}
We can now define a tail-recursive version of |eval| by
calling |load| with an initially empty stack:
\begin{code}
  tail-rec-eval : Expr → Nat
  tail-rec-eval e = load e Top
\end{code}
%
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
    possible input. What it is necessary to demonstrate that the functions
    terminate, so as a corollary the tail-recursive evaluator terminates?

  \item \textbf{Correctness} In the case the tail-recursive evaluator
    terminates, it is correct? By correct it is understood that both the
    evaluation function, |eval|, and  its tail-recursive counterpart,
    |tail-rec-eval|, are extensionally equivalent: for any input both functions
    compute the same result.

  \item  \textbf{Generalization to the \emph{regular} universe} McBride proposes 
    a method for calculating the type of the \emph{stack} from the definition of any type 
    that can be generically expressed in the \emph{regular} universe. Can we
    generalize the results of \textbf{termination} and \textbf{correctness} from
    |Expr| to the generic case?
\end{enumerate}
%
\section{Organization}
\label{sec:intro:org}

  This master thesis is divided in two main parts, with some background material
  at the beginning and conclusions at the end. 

  We start in \Cref{chap:background} giving the reader a broader perspective on
  folds in programming languages to justify the importance of our our work.
  Moreover, in this chapter, we revisit the available literature on techniques
  to assist the termination checker to accept functions that are not defined by
  strictly structural recursion. We end the \namecref{chap:background}, with an
  introduction to generic programming in \Agda~using the \emph{regular}
  universe, which form the basis of our generic tail-recursive evaluator.

  In the first part of the thesis, \Cref{chap:expression}, we show how to
  \emph{manually} write a tail-recursive evaluation function for the type of
  |Expr|, and prove that it terminates and is correct. With this we answer both
  research questions one and two.

  In the second part, \Cref{chap:generic}, we show how to generalize our
  solution for the type |Expr|, from \Cref{chap:expression}, to the generic
  setting. By doing so, we answer the third research question.  
  We conclude this document, in \Cref{chap:conclusion}, with a few remarks about
  the work presented here and discuss possible future work.

\paragraph{Style}

  Before dwelling into the content, we have to remark a few conventions that
  this document follows. The purpose of the code snippets found in this thesis
  is to  guide the reader through the important ideas we present, thus in many
  cases only the type signature of the relevant functions/theorems/datatypes is
  given, and the body is omitted altogether. All code snippets use \Agda~syntax,
  although not all of them directly typecheck. In the type signatures, any
  mentioned variable of type |Set| is taken as implicitly universally
  quantified. To differentiate between `computational' functions and `proving'
  functions (in dependent type theory they are the same thing) we choose to
  prepend the type signatures of the latter with a explicit |forall| quantifier.
  The full code  is freely available online in:
  \medskip
  \begin{center}
  \url{https://github.com/carlostome/Dissection-thesis}
  \end{center}
