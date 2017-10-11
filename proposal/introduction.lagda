
%include polycode.fmt

\section{Introduction}\label{sec:Introduction}

Starting from a small step reduction semantics for a given language, Danvy et al
show a general method for deriving a reduction-free normalization function. The
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
      child { node [leaf] {3}}
      child { node [leaf, hidden] {3} edge from parent[opacity=0.2]};

    \draw [thick] (1,-0.5) -- (1,0.5) node {};
    \node at (1.5,0) [leaf] {3};
    \node at (1.5,-0.5) {\tiny Context};
    \draw [thick] (2,-0.5) -- (2,0.5) node {};
    \node at (0,0.75) {\small Reduction};
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

    \fill[color=red!15] (redex.north) node {}
      -- (redexChildOne.south west) node {}
      -- (redexChildTwo.south east) node {}
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


Functional programming advocates for a style of programming based on higher
order functions over recursive datatypes. This style of programming makes a
clear separating between the patterns behind recursive datastructures and the
functions that operate on them. Concretely given any recursive type built upon
polynomial functors it is posible to give a catamorphism as a general fold. 


- Huet zipper
- McBride Dissection -> Fold into tail recursive machine
- Abstract machine
