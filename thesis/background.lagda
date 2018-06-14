%include background.fmt

\chapter{Background}
\label{chap:background}

% - Fold in a bigger context -> 

% There is a long tradition in the programming language community to 

% understood that semantics of a programming language Programming languages can be studied by writting interpretes for 
% Metalanguages such as ML or Haskell Programming languages represented as AST in a meta
% language.

% duality between tail recursive functions and abstract machines?

% - Denotational semantics of the language can be expresed as a fold in the
% metalanguage.

% - Danvy et al have managed to derive from a one step reduction function (small
% step semantics) a tail recursive abstract machine in ML.

%   -> They state that the problem of doing so in a simply typed metalanguage such as ML 
%      is that the types are not as precise as they could be to rule out cases
%      that cannot happen.

%     Dependently typed programming to the rescue!

%      that are imposible but the type system is not rich enough to  
%   -> Problems is that is not easy to use a theorem prover to verify that the
%   construction they make is correct wrt the initial reduction function.
%   Their construction works in a series of steps that deliver a tail recursive fu

%   - The first part of proving correctness amounts to prove that the function
%     in the metalanguage that performs the reduction free evaluation terminates.
%     The first action of finding the leftmost redex avaliable for reduction is
%     not defined by structural recursion over its arguments thus termination
%     checkers built in theore provers flag the function as non terminating. The
%     overal problem resides is that during the process of doing depth-first search
%     through the input tree where subtrees still to be visited are saved into a
%     Stack (represented by a list) when the search arrives to a point that it has
%     to retrieve a subtree from the stack to proceed with the search and store
%     in the stack a value corresponding to a leaf that is stored in the left
%     subtree of a node, the recursive call is made over a Stack that is not
%     structurally smaller than the input.

    
%     Moreover, 

%     To put it another way, we can think of the stack used to perform the
%     depth-first search over the tree as a execution stack. By making the execution
%     stack explicit we lose the ability to connect the contents of the simply
%     typed stack with the original tree and thus it requires us a great deal of
%     work to use tools such as well founded recursion to convince the theorem
%     prover that something is going smaller during the search.

\section{Termination in Type Theory}
\label{sec:back:term}

\Agda~is a language for describing total functions. General recursive functions
are not allowed as they would render the logic inconsistent. It is not possible
to decide in general if a recursive function terminates, as it will imply that
we have solved the halting problem. To ensure that any defined function
terminates, \Agda~uses a termination checker based on foetus
\cite{Abel98foetus}, that syntactically checks whether the recursive calls of a
function are performed in \textbf{structurally} smaller arguments.

Many interesting --and terminating-- functions that we would like to define do 
not conform to the pattern of being defined by structural recursion. For instance, 
we can consider the sorting function \emph{quicksort} implemented in a functional style:
\begin{code}
  quickSortN : (a -> a -> Bool) -> List a -> List a
  quickSortN p [] = []
  quickSortN p (x :: xs) =  quickSortN p (filter (p x) xs)
                              ++ [ x ] ++
                            quickSortN p (filter (not . (p x)) xs)
\end{code}
\Agda's termination checker marks the function as possibly non-terminating. In
the second clause of the definition, the arguments to both recursive calls,
|filter (p x) xs)| and |filter (not . (p x))| are not structurally smaller than
the input list |x :: xs|. The termination checker has no reason whatsoever to
believe that the application of the function |filter| to the list does not
increase its size. As a contrived example, we could have made a mistake in the
definition of |filter|, replicating elements, so that |quickSort| as defined
above diverges:
%
\begin{code}
  filterBad : (a -> Bool) -> List a -> List a
  filterBad p [] = []
  filterBad p (x :: xs) = if p x  then x :: x :: filterBad p xs
                                  else filterBad p xs

\end{code}
%
On its own, the function |filterBad| is a perfectly valid function that the
termination checker accepts as terminating for any possible input. However, if
called  by any other function, like |quickSort|, that uses its result as a
recursive argument makes such function diverge.  

The termination checker only uses \emph{local} information of the definition of
a function to classify it as terminating or possibly non-terminating.
Concretely, it constructs a graph between the parameters of the function and the
arguments passed to recursive calls and tries to find a well-founded order
amongst them. In any case, calls to other functions are treated as a blackbox.
The reason is that syntactically checking termination conditions is not modular,
as in our example, two terminating functions when combined together may give
rise to a divergent function. 

In case functions are not defined by structural recursion, more advanced tools
are needed to convince the termination checker of termination.  In the rest of
this section, we will explore several available techniques that allow us to
reason within \Agda~about the termination conditions. In particular,
we will discuss how to show to \Agda~that the  |quickSort| example terminates
using: \emph{sized types} (\Cref{subsec:background:sized}), \emph{Bove-Capretta}
predicates (\Cref{subsec:background:bove}) and \emph{well-founded} recursion
(\Cref{subsec:background:wellfounded}).

\subsection{Sized types} 
\label{subsec:background:sized}

Sized types \cite{abel2010miniagda} is a type system extension that allows to
track structural information on the type level. Terms can be annotated with a
type index that represents an \textbf{upper bound} of the actual \textit{size}
of the term being annotated. By size of an inductive datatype it is
understood the number of constructors used to build a value of the type.

Functions can quantify over size variables to relate the size of the
parameters to the size of the result. A term is only well-typed if the 
type system can ensure during type checking that the size type
annotation of a term conforms to its actual size. Size annotations are
gathered during typechecking and passed to a linear inequality solver to check
their validity. The type |Size| used to annotate sizes can be understood as the
type of ordinal numbers without a base element. Its definition is builtin in the
\Agda~compiler, but informally corresponds to the following type:\footnote{To
make clear that |Size| has special treatment, it lives in its own
universe |SizeUniv|.}
%
\begin{code}
  data Size : SizeUniv where
    omega  : Size 
    upOp   : Size -> Size
\end{code}
%
\begin{example}
  We can start the example by defining the type of \textit{sized} lists. The
  difference with the regular definition of list, |List|, is that its signature
  has a new type index of type |Size|. The return type of every constructor
  explicitly instantiates the |Size| index in such a way that the size of the
  recursive occurrences are related to the size of the value being constructed.
  The definition is as follows:
  %
  \begin{code}
  data SList (a : Set) : Size -> Set where
    SNil   : {i : Size} -> SList a i
    SCons  : {i : Size} -> a -> SList a i -> SList a (up i)
  \end{code}
  %
  In the constructor |SNil| there are no recursive occurrences, thus the |Size|
  type-index is universally quantified. On the other hand, in the constructor
  |SCons| the returned |Size| is the size of the recursive parameter, |i|, increased
  by one , |up i|. Indeed, the constructor is adding a new `layer' on top
  of its parameter.

  Using the type-indexed type |SList| we can define a |filter| function, that by
  construction is guaranteed to preserve the size of its input list. We do so by
  explicitly declaring in its type signature that the size of the result does
  not exceed the size of the parameter --the result list does not gain new 
  elements:
  %
  \begin{code}
  filterS : {i : Size} -> (a -> Bool) -> List a i -> List a i
  filterS p SNil          = SNil
  filterS p (SCons x xs)  = if p x  then SCons x (filterS p xs)
                                    else filterS p xs  
  \end{code}
  %
  With this definition of |filter| in hand, we are ready to define the function
  quicksort over the type of size-indexed lists such that it is catalogued as
  terminating by the termination checker:
  %
  \begin{code}
    quickSortS : {i : Size} → (a → a → Bool) → List a i → List a omega
    quickSortS {..(i)}     p (SNil   {i})       = SNil
    quickSortS {..(up i)}  p (SCons  {i} x xs)  
      =  quickSortS {i} p (filter {i} (p x) xs)
           ++ [ x ] ++
         quickSortS {i} p (filter {i} (not ∘ p x) xs)
  \end{code}
  %
  The first thing to note is the use of |omega| as the size annotation in the
  type of the resulting list. The concatenation function, |++Op|, has type |{i j :
  Size} -> List a i -> List a j -> List a omega|, where |omega| indicates
  that we know nothing about the \emph{size} of the resulting list. In fact this is a
  limitation, both theoretical and at the implementation level, of sized
  types.
  The system is not sufficiently expressive to give the function |++Op| a more precise
  type such as | {i j : Size} -> List a i -> List a j -> List a (i + j)|. Nevertheless,
  it is enough to demonstrate to \Agda~ that the implementation of quicksort terminates. 
  Specifically, in the second clause of the definition, the information about the size of the
  input, |up i|, is propagated to the function |filter| that it is known to
  `preserve' the size of its input, thus the recursive call is provably
  terminating. If we try to reimplement the bogus version of filter,
  |filterBad|, using sized types, the definition is not even accepted by the
  typechecker.
\end{example}

  A termination check based on sized types represents an improvement over a
  termination check that works purely in the syntactic level. Sized types allow
  the programmer to introduce semantic annotations about sizes both in types and
  functions so they can be exploited for a more accurate assessment of
  termination. As we showed in the previous example, termination based on sized
  types is modular because it works across the boundaries of function
  definitions. However, the expressively of the system is somewhat limited and in
  general sized types are not first class entities in the language, rather
  builtin objects with special treatment subject to some restrictions.

\todo{there is previous work on sized types by pareto and hughes, abel's work is
only about implementing sized types within dependent types}

\subsection{Bove-Capretta predicate}
\label{subsec:background:bove}

Another technique commonly used in type theory to encode general recursive
functions is the Bove-Capretta\cite{Bove2001} transformation. The call graph of
any function, even if is not defined by structural recursion, posses an inductive 
structure that can be exploited to show termination. Instead of directly
defining the function, the call graph of the original function is added as a new
parameter so the function can be defined by structural recursion over it.

The call graph of a function of type |f : a -> b|, can be made explicit as a
predicate over the input type |a|, |P : a -> Set|. Thus, the possibly
non-terminating function |f| is transformed into another function |f' : a ->
P a -> b| that uses the argument |P a| as the recursive structure. The domain 
predicate |P| outlines the conditions for which the function |f| is known to 
terminate.

However, not everything in the garden is rosy, every time we want to call
function |f'| we have first to prove that the predicate holds on the argument we
supply. Showing that the function terminates for every possible input, amounts
to construct a proof that the predicate holds every element of type |a|, |forall
(x : a) -> P x|. 

\begin{example}

  We now turn our attention to encode the function quicksort using the
  Bove-Capretta technique. The first step is to define the call graph of the
  function as a predicate:
  %
  \begin{code}
  data qsPred (p : a → a → Bool) : List a → Set where
    qsNil   : qsPred p []
    qsCons  : {x : a}  -> {xs : List a}
                       -> qsPred p (filter (p x) xs)
                       -> qsPred p (filter (not . p x) xs) 
                       -> qsPred p (x :: xs)
  \end{code}
  %
  As explained before, the predicate |qsPred| encodes the conditions on which the
  function |quickSort| terminates. The constructor |qsNil| represents the base
  case: quicksort always terminates if the input list is empty. In the inductive
  case, constructor |qsCons|, the termination of quicksort on the input list |x :: xs| 
  depends solely on the termination of quicksort on the inputs |filter (p x) xs| 
  and |filter (not . p x) xs|.

  Thus we can define now a version of the function |quickSort| that is accepted
  by the termination checker by introducing as a new argument the predicate
  |qsPred| applied to the input list:
  %
  \begin{code}
  quickSortBC : (p : a -> a -> Bool)  -> (xs : List a) 
                                      -> qsPred p xs -> List a
  quickSortBC p .. [] qsNil = []
  quickSortBC p ..(x :: xs) (qsCons smaller bigger)
    =  quickSortBC p ((filter (p x) xs)) smaller
         ++ [ x ] ++
       quickSortBC p (filter (not . (p x)) xs) bigger
  \end{code}
  %
  Every time |quickSortBC| is called with a list |xs|, a proof that the
  predicate holds for the specific |xs| has to be constructed, |qsPred p xs|. We
  know that |quickSort| terminates for every possible input, thus it should be
  possible to define a theorem that states that the |qsPred| predicate holds for
  any list of any type:
  %
  \begin{code}
    qsPred-true : forall (p : a -> a -> Bool) -> (xs : List a) -> qsPred p a
    qsPred-true = ...
  \end{code}
  %
  We cannot prove the theorem above by just retrofitting to structural
  recursion, it is just not possible to complete the proof. 
\end{example}

The Bove-Capretta transformation allows the programmer to decouple the task of
defining a function with proving its termination. First, it is enough to outline
the definition of the wanted function and identify its call graph. The
construction of the domain predicate is a fully automatic matter. Nevertheless,
the programmer is required to show every time the function is called that the
input satisfies the predicate.  Even if the function obviously terminates for
every input, showing that the domain predicate holds in general cannot be done
by pattern matching and structural recursion. Showing termination for every
input requires the use of another technique, \emph{well-founded} recursion
(\Cref{subsec:background:wellfounded}).
%{
%format f = "\AF{f}"
%format A = "\AD{A}"
%format B = "\AD{B}"
%format x = "\AB{x}"
%format x1 = "\AB{x_1}"
%format x2 = "\AB{x_2}"
%format x3 = "\AB{x_3}"
%format _<_ = "\AF{\_<\_}"
%format <   = "\AF{<}"

\subsection{Well founded recursion}
\label{subsec:background:wellfounded}

The essential idea of \emph{well founded} recursion is to define a relation over
terms of type |A|, and show that starting from any term of type |A| any
decreasing chain is finite.

% Formally, given a binary relation |<| over |A|, | < : A -> A -> Set |, an
% element |x : A| is accessible if there is no infinite descending chain of the
% form | x > x1 > x2 > x3 ... |. A more constructive characterization of the
% accessibility predicate due to Nordstr{\"o}m \cite{nordstrom1988terminating} is
% the following type in \Agda.

%{Proposal/WellFounded/WellFounded.tex}{Acc}

An element of |A| is accessible if every element smaller than |A| by |<|
is also accessible. The relation |<| is then \emph{well founded} when every
element of |A| is accessible.

%{Proposal/WellFounded/WellFounded.tex}{WF}

The eliminator associated to this type serves us to define recursive functions
over a \emph{well founded} relation.

%{Proposal/WellFounded/WellFounded.tex}{Elim}

\begin{example}
  For encoding the quicksort function using \emph{well founded} recursion, we
  have to define a suitable relation over lists that we can use to show that the
  result of applying |filter| yields a smaller element. We can either use the
  eliminator for \emph{well founded} recursion or define the function by
  explicit recursion over the accessibility predicate. For this matter the proof
  that the relation is \emph{well founded} is mandatory.

  %{Proposal/WellFounded/List.tex}{relation}

  We use the relation less-than over natural numbers to create a new relation
  over lists by appealing to their length. We can lift the proof that less-than
  is \emph{well founded}.

  %{Proposal/WellFounded/List.tex}{WF}

  A couple of lemmas that relate the length of the input list
  to \AF{filter} with the length of the output are also needed.

  %{Proposal/WellFounded/List.tex}{lemma1}
  \vspace*{-0.5cm}
  %{Proposal/WellFounded/List.tex}{lemma2}

  Finally, we can describe quicksort using an auxiliary function that explicitly
  uses the accessibility as the structure in the recursion.

  %{Proposal/WellFounded/List.tex}{QS}

\end{example}

\medskip

A non structurally recursive function,  |f : A -> B|,  can be defined in
\Agda~by giving an smaller-than relation over the input type and performing
structural recursion on the accessibility predicate. For this to work, the
recursive calls should be made over elements that, even though they might not be
structurally smaller than the input, they are smaller by the relation.

Then, for any input value we have to provide a proof that the value is accesible
by the relation, which means all descending chains starting from such element
are finite. If the relation is \emph{well founded}, then every element of the
input type is accesible by the relation giving us a means of constructing
automatically the required proof.

For this reason, defining a function by \emph{well founded} recursion critically
relies on showing that the relation itself is \emph{well founded} which is by no
means an easy task that lastly forces us to show \Agda~that something
structurally decreases.

\medskip

%{
%format 0   = "\AN{0}"
%format aux = "\AF{aux}"
%format Base = "\AD{Base}"
%format Step = "\AD{Step}"
%format succ = "\AD{succ}"
%format zero = "\AD{zero}"
%format y = "\AB{y}"
%format x = "\AB{x}"
%format p = "\AB{p}"
%format <2 = "\AI{\ensuremath{<_{2}}}"

\begin{example}

  Let us consider the natural numbers and two equivalent definitions of the |<|
  (strict less than) relation.
  %{Proposal/WellFounded/Nat.tex}{Rel}
  In the first definition, constructors are peeled off from the first argument
  until there is a difference of one which constitutes the base case. On the
  other hand, the second defintion peels constructors from the left argument
  until it reaches |zero|.

  It should be clear that both definitions are equivalent. However, the first is
  more suitable to prove well foundedness due to the explicit structural relation
  between both arguments.
  %{Proposal/WellFounded/Nat.tex}{Proof-1}
  Pattern matching on the proof allows us to refine both arguments. The
  recursive call to the well foundednees proof in the |Base| case is allowed
  because |y| is structurally smaller than |succ y|. In the step case
  we can recurse using |aux| because the proof |p| is structurally smaller than
  |Step p|.

  Things are not that easy with the second definition. As an attempt we might
  try the following:
  %{Proposal/WellFounded/Nat.tex}{Incomplete}
  The |Base| case requires us to provide a proof of the well foundedness of
  |zero|.  However, we cannot use the well founded proof itself because |zero|
  is not structurally smaller than |succ x|. For the |Step| case we need to
  prove that |succ y| is accesible. We can resort to |aux| and fill the two
  first arguments. However, providing a proof of |succ y <2 succ x| from |p : y
  <2 x| means passing |p| as an argument to the constructors |Step|, the same
  that needed to be peeled in order to be structurally smaller.

  Because there is not a clear relation between the structure of both arguments
  in the proof we cannot use recursive calls and we are stuck.

  In order to solve the problem, we need to introduce an auxiliary lemma that
  relates the structure of both inputs in such a way that pattern matching
  on it refines the arguments clearing the path for the proof of well
  foundedness.

  The required lemma and the proof are as follows:

  %{Proposal/WellFounded/Nat.tex}{Lemma}
  \vspace*{-0.75cm} % remove space between blocks
  %{Proposal/WellFounded/Nat.tex}{Proof-2}
\end{example}
%}

% to add size annotations to the constructors of
% a type. The size of a value represents an upper bound on the number of
% constructors used in its definition.

% Size annoation are attached to inductive types to track the number of
% constructors used in the definition of a value of the type.

% Moreover, functions can be also an
% constructors that a value of a

% \subsection{Bove-Capretta domain predicate}

% Following the Curry-Howard correspondence, if types are to be interpreted as
% propositions and terms inhabiting them as their proofs then termination of terms
% is customary to keep the logic consistent. A non terminating term such as
% |non-term = non-term| could stand as a proof for any proposition (respectively
% as an inhabitanat of any type) thus even a false proposition would have a proof
% backing its truth!


% Moreover, in the dependently typed setting where types can and may depend on terms,
% termination of terms also ensures decidability of the typechecking
% procedure.\arewesure{decidability really depends on termination?}

% Systems based on different flavours of dependent type theory such as Agda or Coq
% \referenceneeded{Agda Coq}


% The traditional approach to ensure termination in systems implementing type
% theory is to restrict the kind of programs that would pass the typechecker.

% By only allowing the user to write function that when performing a recursive
% call this must be made in a structural smaller argument.


% where structural smaller means that a
% constructor or more must be peleed of before performing the recursive call.

% As a first example the implementation of Euclides algorithm for computing the
% greatest common division is analyzed. We state its definition in the following
% snippet.

% In the rest of this section we explore various techniques to approach the
% termination problem in type theory.


% Sized types are a type-based termination checkerk

% \subsection{Bove-Capretta}

% \section{Step back}

