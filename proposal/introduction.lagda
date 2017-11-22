
%include polycode.fmt

\section{Introduction}\label{sec:Introduction}

The functional programming paradigm advocates for a style of programming based
on higher-order functions over inductively defined datatypes. A fold is the
prototypical example of such function.

Using a fold for computation comes at a price. The definition of a fold is not
tail recursive which means that the size of the stack during execution grows
proportionally to the size of the input.

A solution to this problem is to make the stack explicit and define a function
that does tail-recursion over it. The stack reflects the state during the
execution of the fold, thus different data types need to use different types of
stacks.

McBride\cite{McBride:2008:CLM:1328438.1328474} has proposed a method called
dissection to calculate the type of the stack for any data type built from the
identity, constant, product and coproduct functors. By dissecting a type he can
transform a fold into a function that is claimed to be its tail-recursive
counterpart.

However, it is not clear that the resulting function is correct neither that it
terminates. While in the definition of fold the recursive calls are made over
structurally smaller input, this is not the case for the function recursing over
the stack.

The aim of this master thesis is to formalize the notion of dissection and
provide a machine checked proof that it is possible to automatically transform a
fold into a tail recursive function that both terminates and is extensionally
equivalent.


% This 
% counterpart by applying a technique called dissection. The main idea is to
% make the execution stack explicit and define a tail recursive function over it.
% Dissecting a datatype allows for the calculation of the type of stacks.


% The universal property for a fold both used as a computation rule or as a proof
% principle allows a calculational style of programming 

% In this thesis we will try to formalize the notion of dissection in Agda, show
% that 

% As a first example we consider the type of Cons type (lists with the first
% element preceding the rest of the list as opposed to Snoc lists). Defining a
% function , which for a list of Integers results in their sum, can be done both
% using a direct recursive style (left) or by using the fold associated with the
% cons list type.

% -- example of fold vs direct style.

% Some people argue that the use of direct recursive style should be avoided as is
% akin to program in an imperative style by using GOTO statements instead of
% structured loop constructions such as \emph{while} or \emph{for} loops.

% However, the programmer that is inclined to follow this style of programming
% should pay attention to the memory usage of the defined functions. To illustrate
% our point let us consider the reduction of sum [1,2,3,4].

% -- example of reduction (stack is big)

% The problem arises because in order to reduce the addition, both operands must
% be already fully evaluated but the result of the recursive call will not be
% available until the list has been completely traversed.

% A solution to this particular problem is to use the foldl operator.  Because its
% definition is tail recursive, at each step of the computation the addition can
% be evaluated (in non-strict languages some precautions have to be taken) and the
% function runs in constant stack space.

% For lists, the foldl operator solves the problem. However, the foldr combinator
% is not particular of the list type, but any inductively defined datatype comes
% equipped with its own version of fold.

% It is possible to transform a fold into a function that runs in constant stack
% space and is equivalent to the fold?

% Yes it is*. Conor MCBride's seminal paper,Clowns to the Left of Me, Jokers to
% the Right (Pearl): Dissecting Data Structures
% \cite{McBride:2008:CLM:1328438.1328474}, describes a method for transforming a
% function given as the fold of a recursive datatype into a tail recursive
% function.  However, the paper does neither provide a formal proof that the
% resulting function terminates nor that for all inputs the result is the same as
% the original fold.

% The aim of this master thesis is to formalize the notion of dissection and
% provide a machine checked proof that the transformation does terminate and it is
% extensionally equivalent.

% %% END REAL

% Each time a function call is made, before the control flow of the program is
% passed to the function being called, the contents of the local variables are
% be stored in the stack so after the function resumes the result can be computed.

% When a function contains calls to other functions (and possibly itself) but
% the result is directly the result this function is calling, e.g the result of
% the call does not need to be posproccesed in any way, then we say such function
% is tail recursive.

%% END PosREAL

% Indeed it is true that many interested functions can be specified in this way.
% Simple examples such as functions working over lists such as lenght, sum, all
% and even insertion sort can be defined with such pattern.

% - Functional programming

%       * First let us introduce the humble cons list.
%         + It has a definition
%         + It has a foldr
%         We can define some usefull functions for any list using foldr

%       * Higher order functions
%         + Abstract over the concrete recursion pattern of the datatype
%           - The recusion pattern uniquely indentifies the type (with some
%           restrictions of course)
%             | This is true for algebraic datatypes made of sums, products unit
%             and zero.
%             | Functor over recursive positions
%             | Fix point of functor yields isomorphism
%           - The fold is a function that gives a meaning to the type. 
%             | Given an algebra over the base functor, the fold (we call it
%             catamorphism) is uniquely
%             determined.
%           - Somehow an algebra comprises the functions necessary to handle
%           separatedly each constructor of the datatype

%         + Providing functions that can handle the cases we can build a fold
%       * recursive datatypes + folds over them
%         + List is the canonical example
%         + and foldr the canonical fold over lists
%       * elegant
%         + Also considered somehow the functional counterpart to structured
%         programming.
%         + Goto against while/for loops
%           - goto considered harmful
%         + It is much better to use the pattern u want instead of defining the
%           function recursively
%       * concise
%         + separate the recursion pattern from the `logic` of the function
%       * easily understood
%         + Very usable in equational reasoning
%         + Proving properties of programs
%           + Studied a lot by the Squiggol school of calculating programs
%              - Meijer
%              - Bird

%       * There is a problem with this style of programming
%         + The functions are not tail recursive.
%           - Constructors with recursive positions need posprocessing
%           - Large unfinished computations lay on the stack waiting to be
%           evaluated.
%             + They lack the neccesary arguments to proceed (we consider strict
%             functions f bottom = bottom)
%             + They won't be able to initiate the evaluation until the recursion
%             has reached the last element
%             + So the size of the stack grows linearly with the recursive
%             deepness of the value we are computing over.
%             + But stacks are finite entities. Values live in the heap so it is
%             not a problem. Heaps are much larger

%           - If we disregard lazyness, the posprocessing wont occur until all
%             recursive positions have delivered a value.


%         + To apply the function that combines the results of the recursive
%         positions within a concrete constructor is a posprocesor.
%           - This means that until we have a value for each of the recursive
%           positions we canot proceed.
%           - In data which has a high degree of recursive deepnes this has a
%           severe impact on the runtime.
%             - Because for each constructor that contains recursive positions a
%             function is built
%             - In the real world `real execution world` this means that the stack
%             used by the functions grows a big thunk that until we reach the end
%             can't be evaluated

%             - Memory blow
%     + However with no care -> huge number of operations are stacked for being
%                               later processed. -> Memory blow

%     * Tail Recursion
%       + What is tail recursion in functional programming?
%         * The result of the function has to either be a value
%         * Or it should be a call to itself such that there is no posprocessing
%       + Why does tail recursion solves the problem?
%         * Because there is no pending function application, we are not building
%         big expressions in the stack.
%         * We can even claim that the function runs in constant stack space
%       + Good compilers can even perform tail-call optimization
%         * There is an optimization call tail-call that removes the need for a
%         trespasing of flow control. If the last thing u do is a function call
%         without posprocessing then the flow control of the function can be
%         transfered
%       + So a good guess is -> Tail recursion can be a solution?
%         If we can somehow manage to transform a fold into its counterpart we are
%         good. However, does this transformation is good, is well behaved?

%     It is possible to defined this transformation?

%     So we have a function defined as a fold, Do we have a method to transform this
%     fold into a tail recursive function ?

%     - A detour on GP for functors and bifunctors
%       + Functor description
%       + Bifunctors description
%       + Dissection

%     So indeed dissection `does` several things:
%       1. Calculates the type of stacks
%       2. Give us a method to turn a catamorphism into a tail recursive function 
%          very good.

%     However, do we know if this is correct? Are the dissected version and the
%     catamorphism extensionally equal? 

%     We don't even have termination!!! 

%     What is the problem we are facing? load/unload/next recursion is not
%     structurally smaller in neither of its arguments. 

%     We should be able of findind the correct notion of structurally smaller
%     regarding some structure. Maybe the thing is that we havent found the
%     correct pattern of recursion such that indeed the functions are obviously
%     structurally smaller!

%     The quid of the question seems to live in the type of Stack, they do not
%     reflect the pattern of recursion we are looking for. Maybe using dependent
%     types we can change the stack so now it is actually smaller.

%     Maybe an example of how the stack evolves with the execution of load/unload
%     will help us clear the fog a little bit.

%     Back to point one. We have a tail recursive function. aham . How we prove
%     termination?
%       How do we formalize termination and correctness
%       termination in Agda means a function.
%       correctness means extensional equality on functions
%         - We should postulate functional extensionallity
%         - If we are able to show that the transformation terminates somehow we
%           should be able to prove correctness -> It is not even clear WHY it
%           terminatates!

%       + Define what means to be `correct`
%           + Maybe we need extra assumptions. Should the functions have some assumption on them? yes no?
%           - We can study foldr uglys cousing foldl in the search for answers,
%           Who knows!

% * First approximation to prove termination in Agda.
%   + Let us focus not on the generalized version but in McBrides motivation
%   example of trees of expressions

%   + We only care about tail recursion
%   + Small DSL to implement General tail recursive functions (inspired in General
%                                                              from McBride)
%   + What do we gain?
%     - Now its a matter of finding a suitable well-founded relation over
%       stacks+tree, And proving that indeed the functions respect the order
%     - Then we have shown termination



% Functional programming advocates for a style of programming based on
% higher-order functions over recursively defined datatypes.


% Many of the functions
% defined can be expressed as folds. However, if not programmed carefully this may
% lead to a vast usage of resources 



% Beginners and novices to the realm of functional programming usually start by
% definting functions by specifying them in a direct recursive style. For example,
% the length function over list 

% This style, is often considered more elegant and very suitable for performing
% equational reasoning. However, if not programmed careful programs in this style
% may concurr in a vast usage of memory when executed. 

% the recursive equations Functional programming languages such as Haskell, advocate for a style of
% programming that encourages function definitions to be expresed in a recurs

% Functional programming advocates for a style of programming based on higher
% order functions over recursive datatypes. Folds are the paradigmatic way of
% computing functions over the recursive datatypes. Let us consider the example of

% This style of programming makes a
% clear separating between the patterns behind recursive datastructures and the
% functions that operate on them. Concretely given any recursive type built upon
% polynomial functors it is posible to give a catamorphism as a general fold. 

% Starting from a small step reduction semantics for a given term language,
% Danvy\cite{Danvy2009} proposes a general method for deriving a reduction-free normalization function. The
% derived function can be seen as a tail-recursive abstract machine that
% implements the evaluation for arbitrary terms in the language.

% Grosso modo, their method amounts to apply a series of transformations such as
% refocusing, equational simplification, refunctionalization and direct style
% transformation to the function that implements the iteration of the one step
% reduction function.

% As a running example we will consider the evaluation of a Hutton's razor
% language like consisting on either addition of expressions or integer values.
% Besides the abstract syntax of the language we need a explicit notion of
% reduction in the form of a potential redex along with a reduction context.

% % data Expr = Val Int
% %           | Add Expr Expr

% % data Redex = Add Int Int

% % data Context = Empty
% %              | Context\_Left  Int Context
% %              | Context\_Right Expr Context

% A reduction context is a zipper like structure (a Expr with a hole) that
% uniquely determines the part of the tree that is being subject to reduction. A
% decomposition function maps an arbitary expression into a potential redex and a
% reduction context. Then reduction is performed on the redex yielding a value
% that with the reduction context can be used to recompose a tree where the redex
% has been evaluated.

% \begin{figure}
%   \centering
%   \begin{tikzpicture}[sibling distance=12pt]
%   \tikzset{leaf/.append style={rectangle, draw, outer sep=1pt}}
%   \tikzset{internal/.append style={circle, inner sep=1pt, outer sep=1pt}}
%   \tikzset{hidden/.append style={opacity=0.2}}
%   \tikzset{show/.append style={opacity=1}}
%   \tikzstyle{every child}=[sibling distance=10mm, level distance=8mm]

%   \begin{pgfonlayer}{main}
%     \node at (0,0) [internal] {+}
%       child { node (redex) [internal] {+}
%                 child { node (redexChildOne) [leaf] {1} }
%                 child { node (redexChildTwo) [leaf] {2} }
%             }
%       child { node [leaf] {3} };

%     \draw [thick] (1,-0.5) -- (1,0.5) node {};
%     \fill (1.5,0) circle (1pt);
%     \node at (1.5,-0.5) {\tiny Context};
%     \draw [thick] (2,-0.5) -- (2,0.5) node {};

%     \node at (0,-2.25) {\small Redex};

%     % limits
%     \draw [dashed, thick] (2.5,-5) -- (2.5,0.5);
%     \draw [dashed, thick] (-1.5,-2.5) -- (6.5,-2.5);

%     % upper right
%     \begin{scope}[xshift=4.25cm]
%     \node at (0,0) [internal, hidden] {+}
%       child { node [internal] {+}
%                 child { node  [leaf,show] {1} edge from parent[opacity=1]}
%                 child { node  [leaf,show] {2} edge from parent[opacity=1]}
%               edge from parent[opacity=0.2]
%             }
%       child { node [leaf, hidden] {3} edge from parent[opacity=0.2]};

%     \draw [thick] (1,-0.5) -- (1,0.5) node {};
%     \node at (1.5,0) [leaf] {3};
%     \node at (1.5,-0.5) {\tiny Context};
%     \draw [thick] (2,-0.5) -- (2,0.5) node {};
%     \node at (0,-2.25) {\small Decomposition};
%     \end{scope}

%     % lower left
%     \begin{scope}[yshift=-3.5cm]
%     \node at (0,0) [internal, hidden] {+}
%       child { node (reduction) [leaf] {3} edge from parent[opacity=0.2]}
%       child { node [leaf, hidden] {3} edge from parent[opacity=0.2]
%               edge from parent[opacity=0.2]};

%     \draw [thick] (1,-0.5) -- (1,0.5) node {};
%     \node at (1.5,0) [leaf] {3};
%     \node at (1.5,-0.5) {\tiny Context};
%     \draw [thick] (2,-0.5) -- (2,0.5) node {};
%     \node at (0,0.75) {\small Reduction};
%       \node [fill=green!10] (sum) at (-0.5,-1.6) {1\quad +\quad 2};
%       \draw [thick,->] (sum.north) -- node[right] {\tiny reduce}(reduction.south) ;
%     \end{scope}

%     \begin{scope}[xshift=4.25cm,yshift=-3.5cm]
%     \node at (0,0) [internal] {+}
%       child { node [leaf] {3}}
%       child { node [leaf] {3} };

%     \draw [thick] (1,-0.5) -- (1,0.5) node {};
%     \fill (1.5,0) circle (1pt);
%     \node at (1.5,-0.5) {\tiny Context};
%     \draw [thick] (2,-0.5) -- (2,0.5) node {};
%     \node at (0,0.75) {\small Recomposition};
%     \end{scope}
%   \end{pgfonlayer}

%   \begin{pgfonlayer}{background}

%     \fill[color=red!10] ([yshift=0.1cm]redex.north) node {}
%       -- ([xshift=-0.25cm]redexChildOne.south west) node {}
%       -- ([xshift=0.25cm]redexChildTwo.south east) node {}
%       -- cycle;

%   \end{pgfonlayer}

%   \end{tikzpicture}
%     \caption{One step reduction}
%     \label{fig:danvy_tree}
% \end{figure}

% Polynomial functors are a expressive language for describing a variety of
% algebraic datatypes. Building up from the constant, identity, sum and product
% functors are the basic with the addition of a fixed point combinator. By
% introducing a fixed point combinator recursive datatypes can also be encoded.

% A polynomial functor comes equipped with a fold or catamorphism (from the greek
% kata, tear down) that allows us to evaluate

% Any construction from this language
% comes equiped with a fold (or catamorphism).

% If the algebraic datatypes encoded by a polynomial functor were taken as the
% syntax of the language we want to describe, then the fold operation would be
% implementing the semantics, turning arbitrary expressions in our language into
% objects within the semantic domain.

% algebra as small-step semantics

% There is a correspondence between this style of programming and Danvy's work on
% derivation of abstract machines. Indeed, an algebra defined on the pattern
% functor F tells us how to perform a one step evaluation.

% Connor McBride has proposed a method of deriving from a polynomial functor into a
% bifunctor that captures the idea of a traversal 

% Dissection for polynomial functors, those built from the constant, identity sums
% and productus







% What is the research question?/contributions

% It is possible to formalize the idea of in a proof assistant such as Agda




% - Huet zipper
% - McBride Dissection -> Fold into tail recursive machine
% - Abstract machine
