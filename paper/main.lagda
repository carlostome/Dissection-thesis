
%% For double-blind review submission, w/o CCS and ACM Reference (max submission space)
\documentclass[sigplan,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For double-blind review submission, w/ CCS and ACM Reference
%\documentclass[sigplan,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission, w/o CCS and ACM Reference (max submission space)
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For single-blind review submission, w/ CCS and ACM Reference
%\documentclass[sigplan,10pt,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission, w/ required CCS and ACM Reference
%\documentclass[sigplan,10pt]{acmart}\settopmatter{}

% TODO notes
\usepackage[draft]{todonotes}

%% Agda stuff
\usepackage[conor]{agda}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AY}{\AgdaSymbol}
\newcommand{\AN}{\AgdaNumber}
\newcommand{\AS}{\AgdaSpace}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AO}{\AgdaOperator}
\newcommand{\AI}{\AgdaInductiveConstructor}
\newcommand{\AC}{\AgdaCoinductiveConstructor}
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AL}{\AgdaField}
\newcommand{\AR}{\AgdaArgument}
\newcommand{\AT}{\AgdaIndent}
\newcommand{\ARR}{\AgdaRecord}
\newcommand{\AP}{\AgdaPostulate}
\newcommand{\APT}{\AgdaPrimitiveType}


\newcommand{\nonterm}[1]{\hspace*{-0.1cm}\colorbox{orange!25}{#1}}

%% Conference information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\acmConference[PL'17]{ACM SIGPLAN Conference on Programming Languages}{January 01--03, 2017}{New York, NY, USA}
\acmYear{2017}
\acmISBN{} % \acmISBN{978-x-xxxx-xxxx-x/YY/MM}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission;
%% use 'none' for review submission.
\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%\citestyle{acmauthoryear}  %% For author/year citations
%\citestyle{acmnumeric}     %% For numeric citations
%\setcitestyle{nosort}      %% With 'acmnumeric', to disable automatic
                            %% sorting of references within a single citation;
                            %% e.g., \cite{Smith99,Carpenter05,Baker12}
                            %% rendered as [14,5,2] rather than [2,5,14].
%\setcitesyle{nocompress}   %% With 'acmnumeric', to disable automatic
                            %% compression of sequential references within a
                            %% single citation;
                            %% e.g., \cite{Baker12,Baker14,Baker16}
                            %% rendered as [2,3,4] rather than [2-4].


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Note: Authors migrating a paper from traditional SIGPLAN
%% proceedings format to PACMPL format must update the
%% '\documentclass' and topmatter commands above; see
%% 'acmart-pacmpl-template.tex'.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt
%include paper.fmt

\begin{document}

%% Title information
\title[Short Title]{Full Title}         %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
\titlenote{with title note}             %% \titlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'
\subtitle{Subtitle}                     %% \subtitle is optional
\subtitlenote{with subtitle note}       %% \subtitlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{First1 Last1}
\authornote{with author1 note}          %% \authornote is optional;
                                        %% can be repeated if necessary
\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  \position{Position1}
  \department{Department1}              %% \department is recommended
  \institution{Institution1}            %% \institution is required
  \streetaddress{Street1 Address1}
  \city{City1}
  \state{State1}
  \postcode{Post-Code1}
  \country{Country1}                    %% \country is recommended
}
\email{first1.last1@@inst1.edu}          %% \email is recommended

%% Author with two affiliations and emails.
\author{First2 Last2}
\authornote{with author2 note}          %% \authornote is optional;
                                        %% can be repeated if necessary
\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  \position{Position2a}
  \department{Department2a}             %% \department is recommended
  \institution{Institution2a}           %% \institution is required
  \streetaddress{Street2a Address2a}
  \city{City2a}
  \state{State2a}
  \postcode{Post-Code2a}
  \country{Country2a}                   %% \country is recommended
}
\email{first2.last2@@inst2a.com}         %% \email is recommended
\affiliation{
  \position{Position2b}
  \department{Department2b}             %% \department is recommended
  \institution{Institution2b}           %% \institution is required
  \streetaddress{Street3b Address2b}
  \city{City2b}
  \state{State2b}
  \postcode{Post-Code2b}
  \country{Country2b}                   %% \country is recommended
}
\email{first2.last2@@inst2b.org}         %% \email is recommended


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
The functional programming paradigm advocates a style of programming based on
  higher-order functions over inductively defined datatypes. A fold is the
  prototypical example of such a function. However, its use for computation
  comes at a price.  Folds for branching datatype , such as binary trees,
  are by definition not tail recursive functions.

McBride has proposed a method called
  \emph{dissection}\cite{McBride:2008:CLM:1328438.1328474}, to transform a fold
  into its tail-recursive counterpart. Nevertheless, it is not clear why the
  resulting function terminates, nor it is clear that the transformation
  preserves the fold's semantics. In this paper we fill the gap by providing a
  fully machine checked proof of the construction using the proof assistant
  Agda.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003456.10003457.10003521.10003525</concept_id>
<concept_desc>Social and professional topics~History of programming languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{keyword1, keyword2, keyword3}  %% \keywords are mandatory in final camera-ready submission


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle


%{
%format Expr  = "\AD{Expr}"
%format Val   = "\AD{Val}"
%format Add   = "\AD{Add}"
%format eval  = "\AF{eval}"
%format tail-rec-eval  = "\AF{tail\text{-}rec\text{-}eval}"
%format correct = "\AF{correct}"
%format +     = "\AF{+}"
%format Stack = "\AD{Stack}"
%format Top   = "\AD{Top}"
%format Left  = "\AD{Left}"
%format Right = "\AD{Right}"
%format load  = "\AF{load}"
%format unload  = "\AF{unload}"

%format plusOp = "\AF{\_+\_}"

% Bound variables
%format n     = "\AB{n}"
%format e     = "\AB{e}"
%format v     = "\AB{v}"
%format v'     = "\AB{v''}"
%format stk   = "\AB{stk}"
%format e1    = "\AB{\ensuremath{e_1}}"
%format e2    = "\AB{\ensuremath{e_2}}"

\section{Introduction}

The type of binary trees is one of the most simple, yet widespread used,
datastructures in functional programming.  Beyond its elegance and simplicity,
in its definition lies an embarasing truth: a fold over a binary tree is not a
tail recursive function. In order to understand the problem, let us introduce
the type of binary trees.

\begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
\end{code}

We can write an evaluation function that maps binary trees to natural numbers if
we were to interpret the constructor |Add| as addition.

\begin{code}
  eval : Expr -> Nat
  eval (Val n)      = n
  eval (Add e1 e2)  = eval e1 + eval e2
\end{code}

The function |eval| is compositional. The value of a node |Add| is computed by
adding the values denoted by its subexpressions. And here lies the problem. The
operator |\_+\_| needs both of its parameters to be evaluated before it can further
reduce. If the expression we want to compute over is very big this poses a
problem during runtime as the execution stack grows linearly with the size of
the input.

\todo[inline]{Maybe include something about Optimization through tco => get rid of
intermediate steps}

In order to solve the problem, we can make the execution stack explicit and
write a function that performs tail recursion over it. The idea is that we can
use a list to store both intemediate results and the subtress that still need to
be processed. We can define such a stack as follows:

\begin{code}
  data Stack : Set where
    Top    : Stack
    Left   : Expr  -> Stack -> Stack
    Right  : Nat   -> Stack -> Stack
\end{code}

Two mutually recursive functions that operate over the stack and tree are load
and unload. The former traverses a tree finding the leftmost leaf while the
latter dispathes over the stack by accumulating a partial result while looking
for the next subtree.

%{
%format loadN   = "\nonterm{" load "}"
%format unloadN = "\nonterm{" unload "}"
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
%}

A tail recursive version of |eval| can is defined by calling load with the empty
stack.

\begin{code}
  tail-rec-eval : Expr → Nat
  tail-rec-eval e = load e Top
\end{code}

The reader might have noticed that the names of unload and load are higlighted
with yellow. This is because Agda's termination checker flags the pair of
functions as possibly non-terminating. Indeed, the recursive calls are not
always performed over syntactically smaller arguments. If we assumed that it
terminates we still do not know if it is correct in the sense that for every
input |tail-rec-eval| and |eval| agree on the output.

\begin{code}
  correct : forall (e : Expr) -> eval e == tail-rec-eval e
  correct = ??
\end{code}

The main contribution of this paper is to show that we can both prove
termination and correctness of the construction in Agda. Specifically we show
how we can encode an ordering relation over stacks, show that the relation is
well founded and use it to define a tail recursive fold by structural recursion.
We discuss what are the main challenges that we have to overcome to convinde
Agda's termination checker that indeed something `goes smaller`. Moreover, our
approach allows us to get correctness almost for free.

McBride's insight is that we can calculate the type of stacks from the generic
description of a datatype by using Leibniz rules for derivatives. In later
sections of the paper, we discuss how to generalize our results to regular tree
datatypes and by doing so we show that McBride's intuition that the construction
is correct was true.

%}
\section{Basic idea}

\section{Conclusion and future work}

%% Acknowledgments
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
  This material is based upon work supported by the
  \grantsponsor{GS100000001}{National Science
    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
  No.~\grantnum{GS100000001}{nnnnnnn} and Grant
  No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
  conclusions or recommendations expressed in this material are those
  of the author and do not necessarily reflect the views of the
  National Science Foundation.
\end{acks}


%% Bibliography
\bibliography{main}



%% Appendix
\appendix
\section{Appendix}

Text of appendix \ldots

\end{document}
