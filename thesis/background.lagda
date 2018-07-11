%include background.fmt

\chapter{Background}
\label{chap:background}

In this \namecref{chap:background}, we introduce some of the concepts that are
mandatory prerequisites for understanding the main parts of this master thesis.
The chapter is organized into three different sections, whose content is
seemingly unrelated. We begin in \Cref{sec:background:fold} with a broad
overview of semantics in programming languages and its relation to the content
of this master thesis.  In \Cref{sec:background:termination}, we revisit the
literature about techniques for assisting the termination checker of \Agda.
Lastly, in \Cref{sec:background:generic} we quickly overview generic programming
in the context of this thesis. 

\section{A broader perspective}
\label{sec:background:fold}

There are two main approaches for formalizing the semantics of a programming
language: small-step --or operational-- semantics, where for each construct of
the language it is specified how the abstract machine, which is evaluating the
program, evolves; and denotational semantics, where each construct is mapped by
a \emph{mathematical} function to the value it evaluates in the denotational
domain of the language. 

The connection between both style of formalizing the semantics has been
extensively exploited, for example see \cite{Ager:2003:FCE:888251.888254}, to
derive well-known abstract machines, such as the \cite{krivine2007call} machine,
from a denotational semantics specification and vice versa. However, as they
state in the article:

\begin{displayquote}
Most of our implementations of the abstract machines raise compiler warnings
  about non-exhaustive matches. These are inherent to programming abstract
  machines in an ML-like language.
\end{displayquote}

A dependently typed programming language such as \Agda~is a perfect vehicle for
the study and implementation of programming languages. Dependent types can be
fruitfully leveraged for defining both the language, and correspondingly
formalize and verify its semantics either in a small-step or a denotational style.  .
For example, \Citet{swierstra2012mathematics} shows how to derive the
Krivine machine in \Agda~starting from a small-step evaluation semantics for
lambda terms.

However, implementing both a small-step and a denotation function and proving
that they are related is a tedious work that requires some particular expertise. 

From a high level perspective, the denotational semantics of a language is a
function that is both compositional and structurally recursive. For each term,
it specifies how the values that the subterms denote are combined together into
a value for the term on focus. In disguise, the denotation function is just a
fold! The fold is inherent to the inductive structure of the datatype that
represents the language, thus everything is needed is the algebra that for each
constructor determines how to combine the values.

On the other hand, the small-step semantics of a language require some extra
work. As a start, the programming language engineer has to define the
configurations, or internal states, of the machine. Then, she has to specify the
transition rules that govern the machine and finally show, if the language is
strongly normalizing, that iterating the small-step evaluation function
terminates.

The work on this master thesis can be regarded as a step towards exploiting, in
a formal environment such as \Agda, the connection between high-level
denotational functions --in the form of folds-- and low-level abstract machines.
Given a language in terms of its generic representation, and an algebra we
construct a generic tail-recursive function ,i.e. the low-level abstract
machine, that we later formally proof equal to the fold induced by its
structure.

\section{Termination in type theory}
\label{sec:background:termination}

\Agda~is a language for describing total functions. General recursive functions
are not allowed as they would render the logic inconsistent. It is not possible
to decide in general if a recursive function terminates. To ensure that any
defined function terminates, \Agda~uses a termination checker based on foetus
\citep{Abel98foetus}, that syntactically checks whether the recursive calls of a
function are performed over \textbf{structurally} smaller arguments. The
termination checker, however, is not complete: there are programs that terminate
but the termination checker classifies as possibly non terminating.

Many interesting --and terminating-- functions that we would like to define do
not conform to the pattern of being defined by structural recursion. For
instance, the naive tail-recursive evaluator presented in the introduction
(\Cref{sec:intro:descr}). 

In this section, we explore several available techniques which allow us to
reason within \Agda~about termination conditions. Particularly, we revisit
\emph{sized types} (\Cref{subsec:background:sized}), \emph{Bove-Capretta}
predicates (\Cref{subsec:background:bove}) and \emph{well-founded} recursion
(\Cref{subsec:background:wellfounded}).

As a running example, we consider the sorting
function \emph{quicksort} implemented in a functional style:
%
\begin{code}
  quickSortN : (a -> a -> Bool) -> List a -> List a
  quickSortN p [] = []
  quickSortN p (x :: xs) =  quickSortN p (filter (p x) xs)
                              ++ [ x ] ++
                            quickSortN p (filter (not . (p x)) xs)
\end{code}
%
\Agda's termination checker marks the function as possibly non terminating.
In the second clause of the definition, the arguments to both recursive calls,
|filter (p x) xs| and |filter (not . (p x))| are not structurally smaller than
the input list |x :: xs|. The termination checker has no reason whatsoever to
believe that the application of the function |filter| to the list does not
increase its size. As a contrived example, we could have made a mistake in the
definition of |filter|, replicating elements, so that |quickSort| as defined
above may diverge:
%
\begin{code}
  filterBad : (a -> Bool) -> List a -> List a
  filterBad p [] = []
  filterBad p (x :: xs) = if p x  then x :: x :: filterBad p xs
                                  else filterBad p xs

\end{code}
%
On its own, |filterBad| is a perfectly valid function that the termination
checker classifies as terminating for any possible input. However, if any other
function uses its result as a recursive argument, such function could diverge.  

The termination checker only uses \emph{local} information of the definition of
a function to classify it as terminating or possibly non terminating.
Concretely, it constructs a graph between the parameters of the function and the
arguments passed to recursive calls and tries to find a well-founded order
amongst them. In any case, calls to other functions are treated as a blackbox.
The reason is that syntactically checking termination conditions is not modular:
two terminating functions when combined together may give rise to a divergent
function. 

The rest of this section is devoted to show how using the aforementioned
techniques, we can convince \Agda~that |quickSort| terminates on any input.

\subsection{Sized types} 
\label{subsec:background:sized}

Sized types \citep{abel2010miniagda} is a type system extension that allows to
track structural information on the type level. Terms can be annotated with a
type index that represents an \textbf{upper bound} of the actual \textit{size}
of the term being annotated. By size of an inductive datatype it is
understood the number of constructors used to build a value of the type.

Functions can quantify over size variables to relate the size of its
parameters to the size of its result. A term is only well-typed if the 
type system can ensure during type checking that the size type
annotation of a term conforms to its actual size. Size annotations are
gathered during typechecking and passed to a linear inequality solver to check
their validity. The type |Size| used to annotate sizes can be understood as the
type of ordinal numbers without a base element. Its definition is built-in in the
\Agda~compiler, but informally corresponds to the following type:\footnote{The
type |Size| it lives in its own universe |SizeUniv|, this reiterates the special
treatment that is given by the typechecker.}
%
\begin{code}
  data Size : SizeUniv where
    omega  : Size 
    upOp   : Size -> Size
\end{code}
%
Usually, sized types are used to relate the size of the input of a function to
the size of its result. Therefore, sizes in functions are universally quantified
variables that index both the type of the domain and the codomain. For instance,
the identity function over a sized type would be written as:
%
\begin{code}
  idS : {A : Size -> Set} -> {i : Size} -> A i -> A i
  idS x = x
\end{code}

In the next example we explain in more detail how to program with sized types in
order to show that the \emph{quicksort} function always terminates.

\begin{example}
  We start the example by defining the type of \textit{sized} lists. The
  difference with the regular definition of list, |List|, is that its signature
  has a new type index of type |Size|. The return type of every constructor
  explicitly instantiates the |Size| index in such a way that the size of the
  recursive occurrences are related to the size of the value being constructed.
  The definition of sized lists is as follows:
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

  Using the sized type |SList| we define a |filter| function that is guaranteed
  to preserve the size of its input list. We do so by explicitly declaring in
  its type signature that the size of the result does not exceed the size of the
  parameter --the result list does not gain new elements:
  %
  \begin{code}
  filterS : {i : Size} -> (a -> Bool) -> List a i -> List a i
  filterS p SNil          = SNil
  filterS p (SCons x xs)  = if p x  then SCons x (filterS p xs)
                                    else filterS p xs  
  \end{code}
  %
  With this definition of |filter| in hand, we are ready to define the function
  quicksort over the type of sized lists such that it is catalogued as
  terminating by the termination checker:
  %
  \begin{code}
    quickSortS : {i : Size} -> (a -> a -> Bool) -> List a i -> List a omega
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
  limitation, both theoretically and at the implementation level, of sized
  types.
  The system is not sufficiently expressive to give the function |++Op| a more precise
  type such as | {i j : Size} -> List a i -> List a j -> List a (i + j)|. Nevertheless,
  it is enough to demonstrate to \Agda~ that the implementation of quicksort terminates. 
  Specifically, in the second clause of the definition, the information about the size of the
  input, |up i|, is propagated to the function |filter| that it is known to
  preserve the size of its input. The recursive call is now provably
  terminating. 
  
  If we try to reimplement the bogus version of filter, |filterBad|, using sized
  types, its definition is not \emph{well-typed} and the typechecker raises a
  compile-time error.
\end{example}

  A termination check based on sized types represents an improvement over a
  termination check that works purely in the syntactic level. Sized types allow
  the programmer to introduce semantic annotations about sizes both in types and
  functions so they can be exploited for a more accurate assessment of
  termination. As we showed in the previous example, termination based on sized
  types is modular because it works across the boundaries of function
  definitions. However, the expressivity of the system is somewhat limited and in
  general sized types are not first class entities in the language, rather
  built-in objects with special treatment subject to some restrictions.

\subsection{Bove-Capretta predicate}
\label{subsec:background:bove}

Another commonly used technique in type theory to encode general recursive
functions is the Bove-Capretta~\citep{Bove2001} transformation. The call graph of
any function, even if is not defined by structural recursion, posses an inductive 
structure that can be exploited to show termination. Instead of directly
defining the function, the call graph of the original function is added as a new
parameter so the function can be defined by structural recursion over it.

The call graph of a function of type |f : a -> b|, can be made explicit as a
predicate over the input type |a|, |P : a -> Set|. Thus, the possibly
non terminating function |f| is transformed into another function |f' : (x : a) ->
P x -> b| that uses the argument |P x| as the recursive structure. The domain 
predicate |P| outlines the conditions for which the function |f| is known to 
terminate.

However, not everything in the garden is rosy. Every time we want to call
function |f'| we have first to prove that the predicate holds on the argument we
supply. Showing that the function terminates for every possible input, amounts
to construct a proof that the predicate is true for every element of type |a|,
that is |forall (x : a) -> P x|. 

\begin{example}
  \label{example:background:bove}

  We now turn our attention to encode the function quicksort using the
  Bove-Capretta technique. The first step is to define the call graph of the
  function as a predicate:
  %
  \begin{code}
  data qsPred (p : a -> a -> Bool) : List a -> Set where
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
  However, proving the previous theorem is not possible just by structural
  recursion. In order to complete the proof we need a more advanced technique,
  such as \emph{well-founded} recursion (\Cref{subsec:background:wellfounded}).
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
heavily rely on its use. 

The main idea is simple: define a relation over the type of the parameter that
gets `smaller' in each invocation of a function, and show that the relation has
the property of not decreasing indefinitely.

Formally, for a given binary relation over elements of type |a|, | <Op : a -> a
-> Set|, an element |x : a| is \emph{accessible} if there are not infinite descending
chains starting from it by repeated decrements, |x0 < x1 < ... <
xn1 < xn < x|. A more constructive characterization of the accessibility
predicate in type theory, due to \Citet{nordstrom1988terminating}, is
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
smaller elements exists, i.e. |y < x -> Bot|,  constitutes the base case and
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
  \label{example:background:wellfounded-qs}
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
  filter-<L : ∀ (p : a -> Bool) (x : a) (xs : List a) -> filter p xs <L (x :: xs)
  filter-<L p x [] = Base x []
  filter-<L p x (y :: xs) with p y 
  ... | false  = lemma-:: x (filter p xs) (y :: xs) (filter-<L p y xs)
  ... | true   = Step y x (filter p xs) (y :: xs) (filter-<L p y xs)
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
  requirement, specially when is clear that |quickSort| terminates for every
  possible input. To solve this undesirable situation, we can show once and for
  all that every element is accessible. The constructive nature of the
  \emph{well-foundedness} proof (it is an algorithm) serves as procedure to
  build the accessibility predicate without human intervention. The proof of the
  theorem is as follows:
  %
  \begin{code}
  <L-Well-founded : Well-founded <LOp
  <L-Well-founded x = acc (aux x)
    where  aux-Step  : ∀ (x : a) (xs : List a) -> Acc <LOp xs 
                     -> ∀ (y : List a) -> y <L (x :: xs) -> Acc <LOp y
           aux-Step x xs (acc rs)  .. []        (Base .. x .. xs) 
              = acc lambda {_ ()}
           aux-Step x xs (acc rs)  ..(y :: ys)  (Step y .. x ys .. xs p) 
              = acc (aux-Step y ys (rs ys p))

           aux : ∀ (x : List a) -> (y : List a) -> y <L x -> Acc <LOp y
           aux ..(x :: xs) .. [] (Base x xs) = acc lambda { _ ()}
           aux ..(y :: ys) ..(x :: xs) (Step x y xs ys p) 
              = acc (aux-Step x xs (aux ys xs p))

  \end{code}
  %
  The proof follows the usual structure of well-foundedness
  proofs that can be found in the \cite{agdastdlib} standard library. An
  auxiliary function |aux| is used, whose definition is by induction over the
  proof. In the base case, there are no smaller lists than |[]|, thus the proof
  is discharged by appealing to the impossible pattern. In the inductive case,
  where two lists  built up with |::Op| are compared, we need another ancillary
  lemma, |aux-Step|. This lemma says that if the tail of a list |xs| is
  accessible, then any list that results from prepending elements to it is
  accessible too.  It is
  noteworthy to mention that the proof relies on showing the termination checker
  that something \emph{structurally} decreases. In the case of |aux-Step|, the
  proof decreases, while in the function |aux| both the proof and the input get
  smaller.  Nevertheless, when the proof and the input are not related, i.e
  their type does not depend on a common argument, this is not the case.

  Finally, the quicksort function is defined as a wrapper over |quickSortWF|:
  %
  \begin{code}
    quickSort : (a -> a -> Bool) -> List a -> List a
    quickSort p xs = quickSortWF p xs (<L-Well-founded xs)
  \end{code}
\end{example}

The previous example is well engineered to be straightforward. We declare a
relation over lists and the proof of well-foundedness follows almost immediately
from the definition of the relation. Well-founded proofs are not always that
simple, in the next example we examine how the proof is very dependent of the
inductive structure of the
relation.

\begin{example}

  Let us consider the natural numbers and two equivalent definitions of the |<|
  (strict less than) relation:
  %
  \begin{code}

  data Nat : Set where
    zero  : Nat
    suc   : Nat -> Nat

  data <1Op (m : Nat) : Nat -> Set where
    Base1 :                        m <1 suc m
    Step1 : (n : Nat) -> m <1 n ->  m <1 suc n

  data <2Op : Nat -> Nat -> Set where
    Base2 : (n : Nat)                  -> zero   <2 suc n
    Step2 : (n m : Nat)  -> n <2 m      -> suc n  <2 suc m
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
      aux : forall (x : Nat) -> forall (y : Nat) -> y <1 x -> Acc <1Op y
      aux .. (suc y) y Base1        = <1-Well-founded y
      aux .. (suc n) y (Step1 n p)  = aux n y p
  \end{code}
  %
  Pattern matching on the relation allows us to refine both arguments. The
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
  The |Base2| case is effortless: there are no natural numbers smaller than |zero|,
  thus it is eliminated using the impossible pattern. In the inductive case,
  |Step2|, the refined patterns are not adequate to use in a recursive call, the
  arguments are not structurally related.

  To tackle the problem, we have to introduce an auxiliary lemma that links the
  inductive structure of both inputs. Such the lemma states the following:
  %
  \begin{code}
    lemma2 : ∀ (n : Nat) (m : Nat) -> n <2 suc m -> n == m U+ n <2 m
  \end{code}
  %
  Finally, we can complete |<2-Well-founded| proof by appealing to |lemma2| and
  dispatching a recursive call in the inductive case:
  %
  \begin{code}
  <2-Well-founded : Well-founded <2Op
  <2-Well-founded x = acc (aux x)
    where
      aux : (x : Nat) -> forall (y : Nat) -> y <2 x -> Acc <2Op y
      aux zero y ()
      aux (suc x) y p with lemma2 _ _ p
      aux (suc x) .. x p  | inj1 refl  = <2-Well-founded x
      aux (suc x) y p     | inj2 i     = aux x y i
  \end{code}

  This example illustrates how the proof of well-foundedness is totally
  dependent on the choice of the relation. In the first relation, |<1Op|, the
  proof follows directly by induction from the definition, but the second
  relation, |<2Op|, necessitates some extra work and a bit of insight to
  complete the proof.
\end{example}

Using well-founded recursion the programmer can write a non structurally
recursive function directly in \Agda. Before writing such a function, a suitable
relation over the type of elements has to be defined. Moreover, it is necessary
to prove that the argument decreases, by the relation, with each application of
the function.

Then, there are two options: each time the function is called a proof that the
input is accessible by the relation is explicitly supplied, or, the relation is
proven to be well-founded and the proof is used to produce the required evidence.

\section{Generic programming }
\label{sec:background:generic}

There are many opinions on what the term "generic programming" means, depending
on whom you ask. For a thoroughly account of its different flavours, we
recommend the reader to the material by \Citet{10.1007/978-3-540-76786-2_1}.
Nevertheless, a central idea prevails: find a common ground in the
implementation details that can be abstracted away such that when instantiated
can be applied over and over. 

The second part of this master thesis presents a generalization of the
tail-recursive evaluator from part one (\Cref{chap:expression}), on the type
|Expr|, to the "generic" case. What is meant by generic in this context? it
means \textbf{datatype generic}, which Gibbons refers to as \textit{shape
genericity}: abstract over the shape of a datatype, or its inductive structure. 

In the rest of this section, we give a fast-track introduction to generic
programming with dependent types. We put special interest on the \emph{regular}
universe, for which we later, \Cref{chap:generic}, construct the generic tail-recursive 
evaluator.

\subsection{The \emph{regular} universe}
\label{subsec:background:regular}

In a dependently typed programming language such as \Agda, we can represent a
collection of types closed under certain operations as a
\emph{universe}~\citep{altenkirch-mcbride,martin-loef}, that is, a data type |U :
Set| describing the inhabitants of our universe together with its semantics, and
a function, |el : U -> Set|, mapping each element of |U| to its corresponding
type. We have chosen the following universe of \emph{regular}
types~\citep{morris-regular, noort-regular}:
%
\begin{code}
  data Reg : Set1 where
    Zero  : Reg
    One   : Reg
    I     : Reg
    K     : (A : Set) -> Reg
    O+Op  : (R Q : Reg)  -> Reg
    O*Op  : (R Q : Reg) -> Reg
\end{code}
%
Types in this universe are formed from the empty type (|Zero|), unit type
(|One|), and constant types (|K A|); the |I| constructor is used to refer to
recursive subtrees. Finally, the universe is closed under both coproducts
(|O+Op|) and products (|O*Op|). Note that as the constant functor |K| takes 
an arbitrary type |A| as its
argument, the entire datatype lives in |Set1|. This could easily be remedied by
stratifying this universe explicitly and parametrising our development by a base
universe. 
  
We can interpret the inhabitants of |Reg| as a functor of type |Set -> Set|:
\begin{code} 
  interp : Reg -> Set -> Set
  interpl Zero interpr X       = Bot
  interpl One interpr X        = Top
  interpl I interpr X          = X
  interpl (K A) interpr X      = A
  interpl (R O+ Q) interpr X   = interpl R interpr X U+ interpl Q interpr X
  interpl (R O* Q) interpr X   = interpl R interpr X * interpl Q interpr X
\end{code}
To show that this interpretation is indeed functorial, we define the
following law abiding |fmap| operation:
\begin{code}
  fmap : (R : Reg) -> (X -> Y) -> interpl R interpr X -> interpl R interpr Y
  fmap Zero f Empty
  fmap One  f tt            = tt
  fmap I f x                = f x
  fmap (K A) f x            = x
  fmap (R O+ Q) f (inj1 x)  = inj1 (fmap R f x)
  fmap (R O+ Q) f (inj2 y)  = inj2 (fmap Q f y)
  fmap (R O* Q) f (x , y)   = fmap R f x , fmap Q f y
\end{code}

\begin{example}
  We can encode the type of booleans, |Bool|, in the \emph{regular}
  universe. Such type is represented by a code built out of the combination of
  two unit functors, |One|, using the coproduct |O+Op|. The lack of the
  constructor |I| in the code allow us to interpret it over any type we like:
  %
  \begin{code}
    BoolR : Reg
    BoolR = One O+ One

    BoolG : Set 
    BoolG = interpl BoolR interpr Top
  \end{code}
\end{example}
%
The universe as-is forbids the representation of inductive types. Simple
recursive datatypes can be expressed as their underlying pattern functor and a fixed
point that ties the recursion explicitly. In \Agda, the least fixed point of a
functor associated with an element of our universe is defined as follows:
%
\begin{code}
  data mu (R : Reg) : Set where
    In : interpl R interpr (mu R) -> mu R
\end{code}
%
A functor layer given by the code |R| is interpreted by substituting the
recursive positions, marked by the constructor |I|, with generic trees of type
|mu R|. The definition of the fixed point is constrained to functors built
within the universe. In general, the fixed point of a non positive\footnote{The
type being defined appears in negative positions --as a function argument-- in
its own constructors.} type can be used to build non normalizing terms, 
leading to inconsistency.

\begin{example}
  As a first example of a recursive datatype, we show how to encode the usual
  type of cons-lists in the regular universe.  The construction is simple:
  first, we express the \emph{pattern functor} underlying the constructors, |::Op| and
  |[]|, as a generic code of type |Reg|, then the fixed point delivers the
  representation of |List|:
  %
  \begin{code}
    ListR : Set -> Reg
    ListR a = One U+ (K a O+ I)

    ListG : Set -> Set
    ListG a = mu (ListR a)
  \end{code}
  %
  The type |ListG| is the generic representation of the |List| type, and we can
  witness their equivalence by writing a pair of embedding-projection
  functions:
  %
  \begin{code}
    from : {a : Set} -> List a -> ListG a
    from []          = In (inj1 tt)
    from (x :: xs)   = In (inj2 (x , from xs))

    to : {a : Set} -> ListG a -> List a
    to (In (inj1 tt))       = []  
    to (In (inj2 (x , xs))  = x :: to xs
  \end{code}
  %
  That satisfy the following roundtrip properties:
  %
  \begin{code}
    from-to : forall {a : Set} -> (xs : List a   ) -> to (from xs) == xs

    to-from : forall {a : Set} -> (xs : ListG a  ) -> from (to xs) == xs
  \end{code}
\end{example}
%

Next, we can define a \emph{generic} fold, or \emph{catamorphism}, to work on
the inhabitants of the regular universe. For each code |R : Reg|, the |cata R|
function takes an \emph{algebra} of type |interpl R interpr X -> X| as argument.
This algebra assigns semantics to the constructors of | interpl R interpr X|. Folding over a tree
of type |mu R| corresponds to recursively folding over each subtree and
assembling the results using the argument algebra:
%
\begin{spec}
  cataNT : (R : Reg) -> (interpl R interpr X -> X) -> mu R -> X
  cata R alg (In r) = alg (fmap R cataN R alg) r)
\end{spec}
%
Unfortunately, Agda's termination checker does not accept this definition. The
problem, is that the recursive calls to |cata| are not made to structurally
smaller trees, but rather |cata| is passed as an argument to the higher-order
function |fmap|.

To address this, we fuse the |fmap| and |cata| functions into a single
|mapFold| function~\cite{norell-notes}:
\begin{code}
  mapFold : (R Q : Reg) -> (interpl Q interpr X -> X) -> interpl R interpr (mu Q) -> interpl R interpr X
  mapFold Zero     Q alg Empty
  mapFold One      Q alg tt        = tt
  mapFold I        Q alg (In x)    = alg (mapFold Q Q alg x)
  mapFold (K A)    Q alg x         = x
  mapFold (R O+ Q) P alg (inj1 x)  = inj2 (mapFold R P alg x)
  mapFold (R O+ Q) P alg (inj2 y)  = inj2 (mapFold Q P alg y)
  mapFold (R O* Q) P alg (x , y)   = mapFold R P alg x , mapFold Q P alg y
\end{code}
We can now define |cata| in terms of |mapFold| as follows:
\begin{code}
  cata : (R : Reg) (interpl R interpr X -> X) -> mu R -> X
  cata R alg (In r) = mapFold R R alg r
\end{code}
This definition is indeed accepted by Agda's termination checker.

\begin{example}
  We can take the type of expressions from the introduction,
  \Cref{sec:intro:descr}, and encode it in the \emph{regular} universe in two
  steps: first, we define the code of the \emph{pattern functor} underlying the
  constructors; second, the generic representation of |Expr| arises from
  tying the knot over the pattern functor:
  %
  \begin{code}
  ExprR : Reg
  ExprR = K Nat O+ (I O* I)

  ExprG : Set
  ExprG = mu ExprR
  \end{code}
  %
  The type |ExprG| is equivalent to |Expr|, so we can define a embedding-projection pair:
  %
  \begin{code}
    to : ExprG -> Expr
    to (In (inj1 n))          = Val n
    to (In (inj2 (e1 , e2)))  = Add (to e1) (to e2)

    from : Expr -> ExprG
    from (Val n)      = In (inj1 n)
    from (Add e1 e2)  = In (inj2 (from e1 , from e2))
  \end{code}
  %
  The example evaluator, |eval|, is equivalent to a function defined using the
  generic catamorphism, |cata|, that instantiate the code argument with |ExprR|
  and passes as an argument an algebra with |plusOp| and |id|:
  %
  \begin{code}
    eval : ExprG -> Nat
    eval = cata ExprR alg
      where  alg : interpl ExprR interpr Nat -> Nat
            alg (inj1 n)           = n
            alg (inj2 (n , n'))    = n + n'
  \end{code}
\end{example}

Generic programming within the regular universe was first explored by
\cite{noort-regular} in the context of a generic rewriting system written in
\Haskell~\citep{hudak1992report}. The implementation in \Haskell~differs from the
one we have presented here because the language has no support for first class
dependent types (yet). Each code in the universe we defined, |Reg|, is encoded
as a different datatype. Generic functions are written as methods of a
typeclass~\citep{wadler1989make} that is then instantiated to every datatype in
the `universe'. In addition, the library provides a typeclass |Regular| that
uses associated type synonyms~\citep{chakravarty2005associated} to witness the
isomorphism, i.e. embedding-projection pair, between a datatype and its generic
representation.

The regular library has, however, a rather limited expressivity. As the authors
acknowledge:

\begin{displayquote}
 One of the most important limitations of the library described in this paper is
  that it only works for datatypes that can be represented by means of a
  fixed-point. Such datatypes are also known as regular datatypes. This is a
  severe limitation, which implies that we cannot apply the rewriting library to
  nested datatypes or systems of (mutually recursive) datatypes.
\end{displayquote}

Indeed, the regular universe can only represent simple algebraic datatypes.
Datatypes that contain functions --exponentials-- \citep{meijer1995bananas};
that are nested~\citep{nested}; or that are type indexed
~\citep{dybjer-inductive} cannot be encoded in the universe.
