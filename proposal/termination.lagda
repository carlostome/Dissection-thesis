%include proposal.fmt
%include polycode.fmt

\section{Termination}

Agda is a language of total functions, it is only possible to define functions
that are total in the sense that terminate and that they are define for every
possible input value.

General recursion makes the property of termination undecidable in general thus
Agda has a built in termination checker foetus that 


it uses built-in termination checker. that any checks whether the function being defined performs
recursion in structurally smaller arguments. An argument is structurally smaller
when is itself an argument to the constructor the function is pattern matching
on.



However, it is not always the case that the recursive call is performed on an
argument that is structurally smaller.

Every function defined in Agda must be total. General unbounded recursion is
forbidden as would make the logic inconsistent. For this reason, Agda's
termination checker needs to verify that there is a lexicographic order of
parameters in recursive calls that decreases.

Because the termination checker is so restrictive, there are several techniques
have been developed to assist the termination checker.


This is specially the case
where it is not obvious to Agda that the structure of the input is decresing.

The rest of this section is devoted to explain the three main approaches for
assisting Agda's termination checker: well founded recursion, Bove-Capretta
predicate and sized types.

\subsection{Sized types}

Sized types \cite{abel2010miniagda} is a type system extension that allows to
track structural information on the type level. Terms can be annotated with a
\textit{size} index that represents an upper bound of the actual \textit{size}
of the term being annotated. Functions can quantify over type variables and
therefore are able to relate the \textit{size} of their input to the output.

\begin{example}
  We can define the type of \textit{sized} lists in \Agda~by adding a new index
  to the type of lists that tracks size information.

  \InsertCode{Proposal/Sized/List.tex}{List}

  The filter function on lists does not add any new constructor to its input,
  thus we can declare in its type that the function preserves the size bound of
  its argument.

  \InsertCode{Proposal/Sized/List.tex}{Filter}

  Quicksort then is a function from list

  \InsertCode{Proposal/Sized/List.tex}{QS}

  QuickSort is a size preserving function but the size in the type of the output
  list is marked with \AP{ω}

  \InsertCode{Proposal/Sized/List.tex}{append}

\end{example}

\todo{say why sized types do not fit our purpose}

\subsection{Well founded recursion}

The essential idea of \emph{well founded} recursion is to define a relation over terms
of type \AD{A}, and show that starting from any value of \AD{A} it is possible to
reach the smallest element in the relation only using a finite number of steps.

Formally, given a binary relation $<$ over \AD{A}, | _<_ : ad( A ) -> ad(A) ->
Set |, an element $x$ of \AD{A} is accessible if there is no infinite descending chain
of the form $ x > x_1 > x_2 > x_3 \dots $.

A more constructive characterization of the accessibility predicate due to
Nordstr{\"o}m \cite{nordstrom1988terminating} is the following type in \Agda.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{Acc}

An element of \AD{A} is accessible if every element smaller than \AD{A} by |<|
is also accessible. The relation |<| is then \emph{well founded} when every
element of \AD{A} is accessible.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{WF}

The eliminator associated to this type serves us to define recursive functions
over a \emph{well founded} type.

\InsertCode{Proposal/WellFounded/WellFounded.tex}{Elim}

\begin{example}
  QuickSort example

\end{example}

In order to be able to use the eliminator we must first prove that the relation
is well founded. amounts to show \Agda that in the proof there is some argument
that structurally decreases. It can either be the element of the relation or the
proof itself.

\begin{example}

  Let us consider the natural numbers and two equivalent definitions of the |<|
  (strict less than) relation.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Rel}

  In the first definition, constructors are peeled off from the first argument
  until there is a difference of one which constitutes the base case. On the
  contrary, in the second defintion peels constructors from the left argument
  until it reaches \AN{0}.

  It should be clear that both definitions are equivalent. However, the first is
  more suitable to prove well foundedness due to the explicit structural relation
  between both arguments.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Proof-1}

  Pattern matching on the proof allows us to refine both arguments. The
  recursive call to the well foundednees proof in the \AI{Base} case is allowed
  because \AB{y} is structurally smaller than \AI{succ} \AB{y}. In the step case
  we can recurse using \AF{aux} because the proof gets smaller.

  Things are not that easy with the second definition. As an attempt we might
  try the following.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Incomplete}

  The \AI{Base} case requires us to provide a proof of the well foundedness of
  \AN{0}.  However, we cannot use the well founded function itself because it is
  not clear how \AI{zero} is structurally smaller with respect to \AI{succ} \AB{y}.
  The hole in the \AI{Step} case has type which doesn't allow us either to use a
  recursive call on aux.

  Because there is not a clear relation between the structure of both arguments
  in the proof we cannot use recursive calls and we are stuck.

  In order to solve the problem, we need to introduce an auxiliary lemma that
  relates the structure of both inputs in such a way that pattern matching
  on it refines the arguments clearing the path to recursion again.

  The needed lemma and the proof are as follows.

  \InsertCode{Proposal/WellFounded/Nat.tex}{Lemma}
  \vspace*{-0.75cm} % remove space between blocks
  \InsertCode{Proposal/WellFounded/Nat.tex}{Proof-2}
\end{example}






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

