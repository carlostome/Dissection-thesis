%include background.fmt

\chapter{Background}
\label{chap:background}

\section{Fold from a broader perspective}
\label{sec:background:fold}
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
function are performed over \textbf{structurally} smaller arguments.

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
termination checker classifies as terminating for any possible input. However, if
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
reason within \Agda~about termination conditions. In particular, we show to
\Agda~that the  |quickSort| example terminates using: \emph{sized types}
(\Cref{subsec:background:sized}), \emph{Bove-Capretta} predicates
(\Cref{subsec:background:bove}) and \emph{well-founded} recursion
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
  definitions. However, the expressivity of the system is somewhat limited and in
  general sized types are not first class entities in the language, rather
  builtin objects with special treatment subject to some restrictions.

\subsection{Bove-Capretta predicate}
\label{subsec:background:bove}

Another commonly used technique in type theory to encode general recursive
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
to construct a proof that the predicate is true for every element of type |a|, |forall
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
  by the termination checker. We introduce a new parameter, the predicate
  |qsPred| applied to the input list, and recurse over it:
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
  Every time |quickSortBC| is called with a list |xs|, also a proof that the
  predicate holds, |qsPred p xs| has to be supplied. We know that |quickSort|
  terminates for every possible input, thus it should be possible to define a
  theorem that states that the |qsPred| predicate is true for any list of any
  type:
  %
  \begin{code}
    qsPred-true : forall (p : a -> a -> Bool) -> (xs : List a) -> qsPred p a
    qsPred-true = ...
  \end{code}
  %
  However, proving the previous theorem is not possible just by retrofitting to
  structural recursion. In order to complete the proof we need a more advanced
  technique, such as \emph{well-founded} recursion
  (\Cref{subsec:background:wellfounded}).
\end{example}

The Bove-Capretta transformation allows the programmer to decouple the task of
defining a function with proving its termination. First, it is enough to outline
the definition of the wanted function and identify its call graph. The
construction of the domain predicate is a fully automatic matter. Nevertheless,
the programmer is required to show every time the function is called that the
input satisfies the predicate.  Even if the function obviously terminates for
every input, showing that the domain predicate holds in general cannot be done
by pattern matching and structural recursion. 

\subsection{Well-founded recursion}
\label{subsec:background:wellfounded}

The last technique we will discuss is \emph{well-founded} recursion. Amidst the
three, it is the most relevant for this work because the results of this master thesis 
heavily rely on it. 

The main idea is simple: define a relation over the type of the parameter that
is `smaller' in each invocation of the function, and show that the relation has
the property of not decreasing indefinitely.

Formally, for a given binary relation over elements of type |a|, | <Op : a -> a
-> Set|, an element |x : a| is \emph{accessible} if there are not infinite descending
chain starting from it by repeated decrements, |x0 < x1 < ... <
xn1 < xn < x|. A more constructive characterization of the accessibility
predicate, due to Nordstr{\"o}m \cite{nordstrom1988terminating}, is
the following type:
%
\begin{code}
  data Acc (<Op : a -> a -> a) (x : a) : Set where
    acc : (forall (y : a) -> y < x -> Acc <Op y) -> Acc <Op x
\end{code}
%
An element |x : a| is accessible, if every smaller element by the relation is
also accessible. The type |Acc| is inductively defined in such a way that we can
only construct a particular proof of |Acc <Op x| if transitively we can show
that any smaller element is also accessible. A given element, for which no
smaller elements exists, |y < x -> Bot|,  constitutes the base case and
trivially satisfies the predicate.

The recursive structure of the accessibility predicate can be used to turn a non
structurally recursive function into one that is accepted by the termination
checker. A possibly non terminating function |f : a -> a|, is transformed into
another function |f' : (x : a) -> Acc <Op x -> a|, that takes as extra parameter
a proof that the input satisfies the accessibility predicate. The recursive
structure of the |Acc| datatype can be exploited only, if for each invocation of
|f|, we can prove the result to be smaller than the input. 

When another function calls |f'|, it has to explicitly supply a proof
that the concrete input is accessible. If for every element in the relation
there are no infinite descending chains, the relation is \emph{well-founded}.
Thus, for every possible input of a function, defined by structural recursion
over the accessibility predicate, the initial proof needed to kick off the
computation can be algorithmically constructed. We express that a relation is
well-founded as follows:
%
\begin{code}
  Well-founded : (a -> a -> Set) -> Set
  Well-founded <Op = forall x -> Acc <Op x
\end{code}

\begin{example}
  We proceed to show how to encode the quickSort function using well-founded
  recursion. The first step is to define a relation over the input type
  |List|:
  % 
  \begin{code}
  data <LOp : List a -> List a -> Set where
    Base  : (x : a)    (xs : List a)                  -> []         <L (x :: xs)
    Step  : (x y : a)  (xs ys : List a) -> xs <L ys   -> (x :: xs)  <L (y :: ys)
  \end{code}
  % 
  The relation has two constructors:
  \begin{itemize}
    \item The constructor |Base| represents the base case: the empty list is
      always smaller than any list built up with |::Op|.
    \item The inductive case is provided by |Step|. A list |x :: xs| is smaller
      than a list |y :: ys| if inductively the tail of the former is smaller
      than the tail of the latter.
  \end{itemize}
  % 
  In the next step, we define |quickSort| as a function that takes the
  accessibility predicate over the relation as an extra argument and recurse
  over it:
  %
  \begin{code}
  quickSortWF : (a -> a -> Bool)  -> (xs : List a) 
                                  -> Acc <LOp xs -> List a
  quickSortWF p [] (acc rs)         = []
  quickSortWF p (x :: xs) (acc rs)  = 
    quickSortWF p (filter (p x) xs) (rs (filter (p x) xs) ??1)
      ++ [ x ] ++
    quickSortWF p (filter (not . p x) xs) (rs (filter (not . p x) xs) ??2) 
  \end{code}
  % 
  The holes that are left, |??1 : filter (p x) xs <L (x :: xs)| and
  |??2 : filter (not . p x) xs <L (x :: xs)|, necessitate of an ancillary lemma
  expressing that the function filter, no matter what predicate is passed, always
  returns a smaller list: 
  %
  \begin{code}
  filter-<L : ∀ (p : a → Bool) (x : a) (xs : List a) → filter p xs <L (x :: xs)
  filter-<L p x [] = Base x []
  filter-<L p x (y :: xs) with p y 
  ... | false = lemma-:: x (filter p xs) (y :: xs) (filter-<L p y xs)
  ... | true  = Step y x (filter p xs) (y :: xs) (filter-<L p y xs)
  \end{code}
  %
  The definition of |lemma-::| shows that for any lists |ys| and |ys|, if |ys|
  is smaller than |xs|, |ys <L xs|, then regardless of how many elements are
  prepended to |xs|, |ys| remains smaller:
  %
  \begin{code}
  lemma-:: : ∀ (x : a) (ys xs : List a) -> ys <L xs -> ys <L (x :: xs)
  \end{code}
  %
  The lemma is easily completed by induction over the argument |ys|.

  Every time the programmer wants to call |quickSortWF|, she has to produce a
  proof that the input is accessible by |<LOp|. It is burdensome to impose such
  requirement, specially when is clear that |quickSort| terminates for every possible
  input. To solve this undesirable situation, we can show once and for all that
  every element is accessible.The constructive nature of the
  \emph{well-foundedness} proof (is an algorithm) serves as procedure to build
  the accessibility predicate without human intervention. The proof is as
  follows:
  %
  \begin{code}
  <L-Well-founded : Well-founded <LOp
  <L-Well-founded x = acc (aux x)
    where  aux-Step  : ∀ (x : a) (xs : List a) -> Acc <LOp xs 
                     -> ∀ (y : List a) → y <L (x :: xs) → Acc <LOp y
           aux-Step x xs (acc rs)  .. []        (Base .. x .. xs) 
              = acc lambda {_ }
           aux-Step x xs (acc rs)  ..(y :: ys)  (Step y .. x ys .. xs p) 
              = acc (aux-Step y ys (rs ys p))

           aux : ∀ (x : List a) -> (y : List a) -> y <L x -> Acc <LOp y
           aux ..(x :: xs) .. [] (Base x xs) = acc lambda { y ()}
           aux ..(y :: ys) ..(x :: xs) (Step x y xs ys p) 
              = acc (aux-Step x xs (aux ys xs p))

  \end{code}
  %
  The proof follows usual structure of well-foundedness
  proofs that can be found in the standard
  library\footnote{\url{https://github.com/agda/agda-stdlib}} of \Agda. An
  auxiliary function |aux| is used, whose definition is by induction over the
  proof. In the base case, there are no smaller lists than |[]|, thus the proof
  is discharged by appealing to the impossible pattern. In the inductive case,
  where two lists  built up with |::Op| are compared, we need another ancillary
  lemma, |aux-Step|. Such lemma says that if the tail of a list |xs| is
  accessible, then any list that results from prepending elements to it is
  accessible too.  It is
  noteworthy to mention that the proof relies on showing the termination checker
  that something \emph{structurally} decreases. In the case of |aux-Step|, the
  proof decreases, while in the function |aux| both the proof and the input get
  smaller.  Nevertheless, when the proof and the input are not related, i.e they
  are not dependent by their type, this is not the case.

  Finally, the quicksort function is defined as a wrapper over |quickSortWF|:
  %
  \begin{code}
    quickSort : (a -> a -> Bool) -> List a -> List a
    quickSort p xs = quickSortWF p xs (<L-Well-founded xs)
  \end{code}
\end{example}

The previous example is well engineered to be straightforward. We declare a
relation over lists and the proof of well-foundedness follows almost immediately
from the definition of the relation. Not always is as easy, in the next example
we examine how the proof is very dependent of the inductive structure of the
relation.

\begin{example}

  Let us consider the natural numbers and two equivalent definitions of the |<|
  (strict less than) relation.
  %
  \begin{code}

  data Nat : Set where
    zero  : Nat
    suc   : Nat -> Nat

  data <1Op (m : Nat) : Nat -> Set where
    Base1 :                        m <1 suc m
    Step1 : (n : Nat) → m <1 n ->  m <1 suc n

  data <2Op : Nat → Nat → Set where
    Base2 : (n : Nat)                  → zero   <2 suc n
    Step2 : (n m : Nat)  → n <2 m      → suc n  <2 suc m
  \end{code}
  % 
  In the first relation, constructors are peeled off from the first argument
  until there is a difference of one which constitutes the base case. On the
  other hand, in the second relation, the constructors are removed from the left
  argument until |zero| is reached.

  It should be clear that both definitions are equivalent. However, the first is
  more suitable to prove well-foundedness due to the explicit \emph{structural
  relation} between both arguments.
  %
  \begin{code}
  <1-Well-founded : Well-founded <1Op
  <1-Well-founded x = acc (aux x)
    where
      aux : forall (x : Nat) -> forall (y : Nat) → y <1 x → Acc <1Op y
      aux .. (suc y) y Base1        = <1-Well-founded y
      aux .. (suc n) y (Step1 n p)  = aux n y p
  \end{code}
  %
  Pattern matching on the proof allows us to refine both arguments. The
  recursive call to the well-foundednees proof in the |Base| case is allowed
  because |y| is structurally smaller than |suc y|. In the step case
  we can recurse using |aux| because the proof |p| is structurally smaller than
  |Step p|.

  However, things are not that easy with the second definition. As an attempt we might
  try the following:
  %
  \begin{code}
    <2-Well-founded : Well-founded <2Op
    <2-Well-founded x = acc (aux x)
      where
        aux : (x : Nat) -> forall (y : Nat) -> y <2 x -> Acc <2Op y
        aux zero y ()
        aux (suc x) .. zero Base2           = acc lambda { _ ()}
        aux (suc x) .. (suc y) (Step2 y p)  = aux x (suc y) ??
  \end{code}
  %
  The |Base2| case is easy: there are no natural numbers smaller than 0, thus it
  is eliminated using the impossible pattern. In the inductive case, |Step2|,
  the refined patterns are not adequate to use in a recursive call, the
  arguments are not structurally related.

  To tackle the problem, we have to introduce an auxiliary lemma that relates
  structurally both inputs. The lemma is as follows:
  %
  \begin{code}
    lemma2 : ∀ (n : Nat) (m : Nat) -> n <2 suc m → n == m U+ n <2 m
  \end{code}
  %
  Finally, we can complete |<2-Well-founded| proof by appealing to the lemma and
  dispatching a recursive call in the inductive case:
  %
  \begin{code}
  <2-Well-founded : Well-founded <2Op
  <2-Well-founded x = acc (aux x)
    where
      aux : (x : Nat) -> forall (y : Nat) → y <2 x → Acc <2Op y
      aux zero y ()
      aux (suc x) y p with lemma2 _ _ p
      aux (suc x) .. x p  | inj1 refl = <2-Well-founded x
      aux (suc x) y p     | inj2 i    = aux x y i
  \end{code}

  This example illustrates how the proof of well-foundedness is totally dependent on the
  choice of how the relation is defined. In the first relation, |<1Op|, the
  proof follows by induction from the definition, but the second relation,
  |<2Op|, necessitates some extra work and a bit of insight to complete the proof.
\end{example}

Using well-founded recursion the programmer can write a non structurally
recursive function directly in \Agda. Before writing such a function, a suitable
relation over the type of elements that decreases with each application has to
be defined. Moreover, it is necessary a proof showing that the function
delivers a smaller result than the input.

Then, there are two options: each time the function is called a proof that the
input is accessible by the relation is explicitly supplied, or, the relation is
proven to be well-founded and used to produce the required evidence.
