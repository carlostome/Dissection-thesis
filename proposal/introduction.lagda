
%include polycode.fmt

\section{Introduction}\label{sec:Introduction}

The functional programming paradigm advocates for a style of programming based
on higher order functions over recursive datatypes. The recursion pattern
underlying a recursive datatype can be abstracted away in the form of a
\emph{fold} operator. Such functional is uniquely determined and it 
operator uniquely characterizes the structure of the recursive computation.

Instead of writing a recusive function by explicit recursion, the programmer can
take advantage of the `fold` for the datatype. Then and only needs to define
functions that take the recursive solutions for granted.




cases over the datatype constructors, the
recursion pattern of a datatype is abstracted away leaving the obligation 



The recursion pattern of a
datatype can be abstracted away, leaving the programmer with the obligation of   because any recursively defined function over
it can be defined in terms of a fold. Given a datatype, the fold is the function
that captures how the recursive structure of the type has to be exploited. Such
Being the fold uniquely determined means that the programmer would only need to
focus on defining how the different cases of the datatype have to be handled to
arrive at a solution.


uniquely determines how a recursive function over such is to be
computed.


If the recursion pattern of
the datatype in cuestion is abstracted away, then the programmer is left with
filling the interesting parts of the computation. This is how solutions to
smaller problems are to be combined for a solution to the problem.  The former
construction works, because the function that performs the actual recursion, the
fold or catamorphism, is uniquely determined by the datatype itself.

As a paradigmatic example of this, the Cons list in our favourite general purpose
functional programming language Haskell

and the fol, which leaves the programmer with the
only obligation of articulating how the solution to the 


and the leaving the programmer the
obligation to only fill in the interesting parts of the program.


The functional programming paradigm advocates for a style of programming based
on higher-order functions over recursive datatypes. Functions defined in this
style are often concise, easily understandable and elegant. Moreover, when
proving properties of functions via equatioal  When the pattern of
recursion underlying the structure of the type the function is working on we get
a better and more concise definition of a function. As goto are considered the
example of a bad practice in the 

Indeed it is true that many interested functions can be specified in this way.
Simple examples such as functions working over lists such as lenght, sum, all
and even insertion sort can be defined with such pattern.

- Functional programming

      * First let us introduce the humble cons list.
        + It has a definition
        + It has a foldr
        We can define some usefull functions for any list using foldr

      * Higher order functions
        + Abstract over the concrete recursion pattern of the datatype
          - The recusion pattern uniquely indentifies the type (with some
          restrictions of course)
            | This is true for algebraic datatypes made of sums, products unit
            and zero.
            | Functor over recursive positions
            | Fix point of functor yields isomorphism
          - The fold is a function that gives a meaning to the type. 
            | Given an algebra over the base functor, the fold (we call it
            catamorphism) is uniquely
            determined.
          - Somehow an algebra comprises the functions necessary to handle
          separatedly each constructor of the datatype

        + Providing functions that can handle the cases we can build a fold
      * recursive datatypes + folds over them
        + List is the canonical example
        + and foldr the canonical fold over lists
      * elegant
        + Also considered somehow the functional counterpart to structured
        programming.
        + Goto against while/for loops
          - goto considered harmful
        + It is much better to use the pattern u want instead of defining the
          function recursively
      * concise
        + separate the recursion pattern from the `logic` of the function
      * easily understood
        + Very usable in equational reasoning
        + Proving properties of programs
          + Studied a lot by the Squiggol school of calculating programs
             - Meijer
             - Bird

      * There is a problem with this style of programming
        + The functions are not tail recursive.
          - Constructors with recursive positions need posprocessing
          - Large unfinished computations lay on the stack waiting to be
          evaluated.
            + They lack the neccesary arguments to proceed (we consider strict
            functions f bottom = bottom)
            + They won't be able to initiate the evaluation until the recursion
            has reached the last element
            + So the size of the stack grows linearly with the recursive
            deepness of the value we are computing over.
            + But stacks are finite entities. Values live in the heap so it is
            not a problem. Heaps are much larger

          - If we disregard lazyness, the posprocessing wont occur until all
            recursive positions have delivered a value.


        + To apply the function that combines the results of the recursive
        positions within a concrete constructor is a posprocesor.
          - This means that until we have a value for each of the recursive
          positions we canot proceed.
          - In data which has a high degree of recursive deepnes this has a
          severe impact on the runtime.
            - Because for each constructor that contains recursive positions a
            function is built
            - In the real world `real execution world` this means that the stack
            used by the functions grows a big thunk that until we reach the end
            can't be evaluated

            - Memory blow
    + However with no care -> huge number of operations are stacked for being
                              later processed. -> Memory blow

    * Tail Recursion
      + What is tail recursion in functional programming?
        * The result of the function has to either be a value
        * Or it should be a call to itself such that there is no posprocessing
      + Why does tail recursion solves the problem?
        * Because there is no pending function application, we are not building
        big expressions in the stack.
        * We can even claim that the function runs in constant stack space
      + Good compilers can even perform tail-call optimization
        * There is an optimization call tail-call that removes the need for a
        trespasing of flow control. If the last thing u do is a function call
        without posprocessing then the flow control of the function can be
        transfered
      + So a good guess is -> Tail recursion can be a solution?
        If we can somehow manage to transform a fold into its counterpart we are
        good. However, does this transformation is good, is well behaved?

    It is possible to defined this transformation?

    So we have a function defined as a fold, Do we have a method to transform this
    fold into a tail recursive function ?

    - A detour on GP for functors and bifunctors
      + Functor description
      + Bifunctors description
      + Dissection

    So indeed dissection `does` several things:
      1. Calculates the type of stacks
      2. Give us a method to turn a catamorphism into a tail recursive function 
         very good.

    However, do we know if this is correct? Are the dissected version and the
    catamorphism extensionally equal? 

    We don't even have termination!!! 

    What is the problem we are facing? load/unload/next recursion is not
    structurally smaller in neither of its arguments. 

    We should be able of findind the correct notion of structurally smaller
    regarding some structure. Maybe the thing is that we havent found the
    correct pattern of recursion such that indeed the functions are obviously
    structurally smaller!

    The quid of the question seems to live in the type of Stack, they do not
    reflect the pattern of recursion we are looking for. Maybe using dependent
    types we can change the stack so now it is actually smaller.

    Maybe an example of how the stack evolves with the execution of load/unload
    will help us clear the fog a little bit.

    Back to point one. We have a tail recursive function. aham . How we prove
    termination?
      How do we formalize termination and correctness
      termination in Agda means a function.
      correctness means extensional equality on functions
        - We should postulate functional extensionallity
        - If we are able to show that the transformation terminates somehow we
          should be able to prove correctness -> It is not even clear WHY it
          terminatates!

      + Define what means to be `correct`
          + Maybe we need extra assumptions. Should the functions have some assumption on them? yes no?
          - We can study foldr uglys cousing foldl in the search for answers,
          Who knows!

* First approximation to prove termination in Agda.
  + Let us focus not on the generalized version but in McBrides motivation
  example of trees of expressions

  + We only care about tail recursion
  + Small DSL to implement General tail recursive functions (inspired in General
                                                             from McBride)
  + What do we gain?
    - Now its a matter of finding a suitable well-founded relation over
      stacks+tree, And proving that indeed the functions respect the order
    - Then we have shown termination



Functional programming advocates for a style of programming based on
higher-order functions over recursively defined datatypes.


Many of the functions
defined can be expressed as folds. However, if not programmed carefully this may
lead to a vast usage of resources 



Beginners and novices to the realm of functional programming usually start by
definting functions by specifying them in a direct recursive style. For example,
the length function over list 

This style, is often considered more elegant and very suitable for performing
equational reasoning. However, if not programmed careful programs in this style
may concurr in a vast usage of memory when executed. 

the recursive equations Functional programming languages such as Haskell, advocate for a style of
programming that encourages function definitions to be expresed in a recurs

Functional programming advocates for a style of programming based on higher
order functions over recursive datatypes. Folds are the paradigmatic way of
computing functions over the recursive datatypes. Let us consider the example of

This style of programming makes a
clear separating between the patterns behind recursive datastructures and the
functions that operate on them. Concretely given any recursive type built upon
polynomial functors it is posible to give a catamorphism as a general fold. 

Starting from a small step reduction semantics for a given term language,
Danvy\cite{Danvy2009} proposes a general method for deriving a reduction-free normalization function. The
derived function can be seen as a tail-recursive abstract machine that
implements the evaluation for arbitrary terms in the language.

Grosso modo, their method amounts to apply a series of transformations such as
refocusing, equational simplification, refunctionalization and direct style
transformation to the function that implements the iteration of the one step
reduction function.

As a running example we will consider the evaluation of a Hutton's razor
language like consisting on either addition of expressions or integer values.
Besides the abstract syntax of the language we need a explicit notion of
reduction in the form of a potential redex along with a reduction context.

% data Expr = Val Int
%           | Add Expr Expr

% data Redex = Add Int Int

% data Context = Empty
%              | Context\_Left  Int Context
%              | Context\_Right Expr Context

A reduction context is a zipper like structure (a Expr with a hole) that
uniquely determines the part of the tree that is being subject to reduction. A
decomposition function maps an arbitary expression into a potential redex and a
reduction context. Then reduction is performed on the redex yielding a value
that with the reduction context can be used to recompose a tree where the redex
has been evaluated.

\begin{figure}
  \centering
  \begin{tikzpicture}[sibling distance=12pt]
  \tikzset{leaf/.append style={rectangle, draw, outer sep=1pt}}
  \tikzset{internal/.append style={circle, inner sep=1pt, outer sep=1pt}}
  \tikzset{hidden/.append style={opacity=0.2}}
  \tikzset{show/.append style={opacity=1}}
  \tikzstyle{every child}=[sibling distance=10mm, level distance=8mm]

  \begin{pgfonlayer}{main}
    \node at (0,0) [internal] {+}
      child { node (redex) [internal] {+}
                child { node (redexChildOne) [leaf] {1} }
                child { node (redexChildTwo) [leaf] {2} }
            }
      child { node [leaf] {3} };

    \draw [thick] (1,-0.5) -- (1,0.5) node {};
    \fill (1.5,0) circle (1pt);
    \node at (1.5,-0.5) {\tiny Context};
    \draw [thick] (2,-0.5) -- (2,0.5) node {};

    \node at (0,-2.25) {\small Redex};

    % limits
    \draw [dashed, thick] (2.5,-5) -- (2.5,0.5);
    \draw [dashed, thick] (-1.5,-2.5) -- (6.5,-2.5);

    % upper right
    \begin{scope}[xshift=4.25cm]
    \node at (0,0) [internal, hidden] {+}
      child { node [internal] {+}
                child { node  [leaf,show] {1} edge from parent[opacity=1]}
                child { node  [leaf,show] {2} edge from parent[opacity=1]}
              edge from parent[opacity=0.2]
            }
      child { node [leaf, hidden] {3} edge from parent[opacity=0.2]};

    \draw [thick] (1,-0.5) -- (1,0.5) node {};
    \node at (1.5,0) [leaf] {3};
    \node at (1.5,-0.5) {\tiny Context};
    \draw [thick] (2,-0.5) -- (2,0.5) node {};
    \node at (0,-2.25) {\small Decomposition};
    \end{scope}

    % lower left
    \begin{scope}[yshift=-3.5cm]
    \node at (0,0) [internal, hidden] {+}
      child { node (reduction) [leaf] {3} edge from parent[opacity=0.2]}
      child { node [leaf, hidden] {3} edge from parent[opacity=0.2]
              edge from parent[opacity=0.2]};

    \draw [thick] (1,-0.5) -- (1,0.5) node {};
    \node at (1.5,0) [leaf] {3};
    \node at (1.5,-0.5) {\tiny Context};
    \draw [thick] (2,-0.5) -- (2,0.5) node {};
    \node at (0,0.75) {\small Reduction};
      \node [fill=green!10] (sum) at (-0.5,-1.6) {1\quad +\quad 2};
      \draw [thick,->] (sum.north) -- node[right] {\tiny reduce}(reduction.south) ;
    \end{scope}

    \begin{scope}[xshift=4.25cm,yshift=-3.5cm]
    \node at (0,0) [internal] {+}
      child { node [leaf] {3}}
      child { node [leaf] {3} };

    \draw [thick] (1,-0.5) -- (1,0.5) node {};
    \fill (1.5,0) circle (1pt);
    \node at (1.5,-0.5) {\tiny Context};
    \draw [thick] (2,-0.5) -- (2,0.5) node {};
    \node at (0,0.75) {\small Recomposition};
    \end{scope}
  \end{pgfonlayer}

  \begin{pgfonlayer}{background}

    \fill[color=red!10] ([yshift=0.1cm]redex.north) node {}
      -- ([xshift=-0.25cm]redexChildOne.south west) node {}
      -- ([xshift=0.25cm]redexChildTwo.south east) node {}
      -- cycle;

  \end{pgfonlayer}

  \end{tikzpicture}
    \caption{One step reduction}
    \label{fig:danvy_tree}
\end{figure}

Polynomial functors are a expressive language for describing a variety of
algebraic datatypes. Building up from the constant, identity, sum and product
functors are the basic with the addition of a fixed point combinator. By
introducing a fixed point combinator recursive datatypes can also be encoded.

A polynomial functor comes equipped with a fold or catamorphism (from the greek
kata, tear down) that allows us to evaluate

Any construction from this language
comes equiped with a fold (or catamorphism).

If the algebraic datatypes encoded by a polynomial functor were taken as the
syntax of the language we want to describe, then the fold operation would be
implementing the semantics, turning arbitrary expressions in our language into
objects within the semantic domain.

algebra as small-step semantics

There is a correspondence between this style of programming and Danvy's work on
derivation of abstract machines. Indeed, an algebra defined on the pattern
functor F tells us how to perform a one step evaluation.

Connor McBride has proposed a method of deriving from a polynomial functor into a
bifunctor that captures the idea of a traversal 

Dissection for polynomial functors, those built from the constant, identity sums
and productus







What is the research question?/contributions

It is possible to formalize the idea of in a proof assistant such as Agda




- Huet zipper
- McBride Dissection -> Fold into tail recursive machine
- Abstract machine
