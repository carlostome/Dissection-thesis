\documentclass{beamer}
\usepackage{beamerthemeuucs}
\setbeamercovered{transparent} 
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{bbold} %% Font for fancy math letters
\usepackage{dsfont} %% Font for fancy math letters
\usepackage{scalerel}
% \usepackage{enumitem}
% \usepackage{showframe}

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
\newcommand{\hole}[1]{\colorbox{yellow!50}{\ensuremath{\bigbox_{#1}}}}

\usepackage{tikz}
\usetikzlibrary{arrows,snakes,backgrounds,calc}
\newcommand{\pgftextcircled}[1]{
    \setbox0=\hbox{#1}%
    \dimen0\wd0%
    \divide\dimen0 by 2%
    \begin{tikzpicture}[baseline=(a.base)]%
        \useasboundingbox (-\the\dimen0,0pt) rectangle (\the\dimen0,1pt);
        \node[circle,draw,outer sep=0pt,inner sep=0.1ex] (a) {\textbf{#1}};
    \end{tikzpicture}
}

%include presentation.fmt

\renewcommand\hscodestyle{%
   \setlength\leftskip{0.1cm}%
   \small
}
\title{Verified tail-recursive folds through dissection}
\subtitle{Thesis defense}
\author{Carlos Tomé Cortiñas}
\date{\today}
\begin{document}
\frame{\titlepage}

%{ beginning of part1
%include part1.fmt

\section{Introduction}
\subsection{Motivation}

\frame{
  \frametitle{|Expr|ession language}
  \begin{code}
  data Expr : Set where
    Val  :  Nat   -> Expr
    Add  :  Expr  -> Expr -> Expr
  \end{code}

  \pause

  \begin{minipage}[c]{0.55\textwidth}
    \begin{code}
      expr1 : Expr
      expr1 = Add  (Val 1) 
                    (Add  (Val 2) 
                          (Val 2))
    \end{code}
  \end{minipage}
  \pause
  \begin{minipage}[c]{0.35\textwidth}
    \input{figures/figure1}
  \end{minipage}
}

\note{
  Purpose: Introduce expressions
  \begin{itemize}
    \item Arithmetic expressions
    \item Example expression and AST
  \end{itemize}

}

\frame{
  \frametitle{Evaluating |Expr|essions}
  \begin{code}
    eval : Expr -> Nat
    eval (Val n)      = n
    eval (Add e1 e2)  = eval e1 + eval e2
  \end{code}

  \pause 
  \vspace*{-0.5cm}
  \begin{code}
    prop1 : eval expr1 == 5
    prop1 = refl
  \end{code}

  \pause

  {\Large Is there a \textbf{problem} with |eval|?}
}

\note{
  Purpose: Evaluator over expressions
  \begin{itemize}
    \item Map an expr to a natural number
    \item Compositional and structurally recursive
  \end{itemize}
}

\frame{
  \frametitle{Evaluating |Expr|essions (2)}

  \begin{code}
    eval : Expr -> Nat
    eval (Val n)      = n
    eval (Add e1 e2)  = eval e1 + eval e2
  \end{code}

  |eval  (Add (Val 1) (Add  (Val 2)  (Val 2))|

  \pause

  \vspace*{-1em}
  \begin{center}
    \begin{itemize}
      \setlength{\itemindent}{2em}
      \uncover<2>{\item[|~>|] | eval (Val 1)  + eval (Add  (Val 2)  (Val 2))|}
      \uncover<3>{\item[|~>|] | 1             + eval (Add (Val 2) (Val 2))|}
      \uncover<4>{\item[|~>|] | 1             + (eval (Val 2) + eval (Val 2))|}
      \uncover<5>{\item[|~>|] | 1             + (2 + eval (Val 2)) ...|}
    \end{itemize}
  \end{center}
        
}

\note{
  Purpose: Show few steps of evaluation
  \begin{itemize}
      \item 1 + 2 + are stored as continuations on the stack
  \end{itemize}
}

\frame{
  \frametitle{Evaluating |Expr|essions (3)}

  \begin{code}
    Add (Val 1) (Add (Val 2) (Add (Val 3) (Add (Val 4) ...
  \end{code}

  \pause

  \begin{code}
    1 + (2 + (3 + (4 + ...
  \end{code}
        
  \pause

  \begin{itemize}[<+->]
    \item The execution \textit{stack} grows linearly with the size of the |Expr|
    \item \alert{Stack Overflow!} 
  \end{itemize}

  \pause[\thebeamerpauses]

  \begin{center}
    {\Large A \textbf{well-typed} program \textit{went wrong}\footnote{Robin
    Milner does not approve}}
  \end{center}
}

\note{
  Purpose: Present the problem
  \begin{itemize}
      \item Degenerate case
      \item too many continuations on the stack
  \end{itemize}
}

\frame{
  \frametitle{A solution}

  \begin{itemize}
    \item Make the \textit{stack} explicit
    \item Write a \textit{tail-recursive} function that recurses over it
  \end{itemize}

  \pause
  \begin{code}
    data Stack : Set where
      Top    : Stack
      Left   : Expr  -> Stack -> Stack
      Right  : Nat   -> Stack -> Stack
  \end{code}
}

\note{
  Purpose: Introduce the buggy solution
  \begin{itemize}
      \item Evaluation left-to-right
      \item Stack results for left subtrees constructor |Right|
      \item Stack unevaluated subtrees constructor |Left|
  \end{itemize}
}

\frame{
  \frametitle{A solution (2)}

\begin{code}
  mutual
    load : Expr -> Stack -> Nat
    load (Val n)      stk = unload1 n stk
    load (Add e1 e2)  stk = load e1 (Left e2 stk)

    unload1 : Nat -> Stack -> Nat
    unload1 v   Top             = v
    unload1 v   (Right v' stk)  = unload1 (v' + v) stk
    unload1 v   (Left e stk)    = load e (Right v stk)
\end{code}

\pause

\vspace*{-1em}
\begin{code}
  tail-rec-eval : Expr -> Nat
  tail-rec-eval e = load e Top
\end{code}
}

\note{
  Purpose: Explain load and unload
  \begin{itemize}
      \item load stores right subexpressions on the stack
      \item unload traverses the stack looking for subexpressions to process and
        accumulating partial results
      \item The evaluator just calls load with the empty stack
  \end{itemize}
}

\frame{
  \frametitle{|load| and |unload1|}

  \begin{center}
    \only<1>{|load (Add (Val 1) (Add (Val 2) (Val 2))) Top|}
    \only<2>{|load (Val 1) (Left (Add (Val 2) (Val 2)) Top)|}
    \only<3>{|unload1 1 (Left (Add (Val 2) (Val 2)) Top)|}
    \only<4>{|load (Add (Val 2) (Val 2)) (Right 1 Top)|}
    \only<5>{|load (Val 2) (Left (Val 2) (Right 1 Top))|}
    \only<6>{|unload1 2 (Left (Val 2) (Right 1 Top))|}
    \only<7>{|load (Val 2) (Right 2 (Right 1 Top))|}
    \only<8>{|unload1 2 (Right 2 (Right 1 Top))|}
    \only<9>{|unload1 (2 + 2) (Right 1 Top)|}
    \only<10>{|unload1 4 (Right 1 Top)|}
    \only<11>{|unload1 (1 + 4) Top|}
    \only<12>{|unload1 5 Top|}

    \input{figures/figure2}
  \end{center}
}

\note{
  Purpose: Illustrate load and unload
  \begin{itemize}
      \item load goes left down
      \item unload goes right up
  \end{itemize}
}

\frame{
  \frametitle{Problem solved?}
  {\Large Have we \textbf{actually} solved the problem?}
  \pause
  \begin{itemize}[<+->]
      \item It seems so, however ...
      \item How do we know that 
        
        \begin{center}
        |forall (e : Expr) -> tail-rec-eval e == eval e| ?
        \end{center}
      \item We \textbf{don't} know, we \textbf{don't} have a \textit{mathematical proof}
      \item Let's \textit{produce} it!
  \end{itemize}
}

\frame{
  \frametitle{Problem solved? (2)}
  \begin{itemize}[<+->]
    \item Is \textbf{not} that easy; \textit{tail-recursion} has come at a \textbf{price}
  \end{itemize}
  \pause[\thebeamerpauses]
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload1 v   Top             = v
    unload1 v   (Right v' stk)  = unloadN (v' + v) stk
    unload1 v   (Left e stk)    = loadN e (Right v stk)
\end{code}

\note{
  Purpose: Solution bad
  \begin{itemize}
      \item Is not accepted by the termination checker
      \item If we cannot prove termination we cannot prove correctness
  \end{itemize}
}

}

\subsection{Contributions of this Master Thesis}
\frame{
  \frametitle{Contributions}
  \pause
  \begin{itemize}[<+->]
    \item We construct a provably \textbf{terminating} tail-recursive function \textit{similar} to |tail-rec-eval|
    \item We prove it \textbf{correct} with respect to |eval|
    \item We \textbf{generalize} our results to any fold over any (simple)
      algebraic datatype using McBride's notion of \textit{dissection}
  \end{itemize}
  \pause[\thebeamerpauses]
  \begin{center}
    We have formalized everything in \textbf{Agda}
  \end{center}
}

\section*{Outline}
\frame{\tableofcontents[hideallsubsections]}

\section{A tail-recursive evaluator for |Expr|}

\frame{
  \frametitle{Problematic call}
\begin{code}
  mutual
    loadN : Expr -> Stack -> Nat
    load (Val n)      stk = unloadN n stk
    load (Add e1 e2)  stk = loadN e1 (Left e2 stk)

    unloadN : Nat -> Stack -> Nat
    unload1 v   Top             = v
    unload1 v   (Right v' stk)  = unloadN (v' + v) stk
    unload1 v   (Left e stk)    = loadN e (Right v stk)
\end{code}
}
\note{
  Purpose: |load| and |unload1| not accepted by termination checker
  \begin{itemize}
      \item Not structurally recursive
      \item Termination checker needed to guarantee soundness
  \end{itemize}
}

\frame{
  \frametitle{Terminating |load| and |unload1|}
  \begin{itemize}
    \item We rewrite |load| and |unload1| so that they are \textbf{obviously} terminating
  \end{itemize}

  \begin{code}
    ZipperType = Nat * Stack
  \end{code}

  \pause
  \vspace*{-1.0em}
  \begin{code}
    unload1 : Nat -> Stack -> ZipperType U+ Nat
    unload1 v   Top             = inj2 v
    unload1 v   (Right v' stk)  = unload1 (v' + v) stk
    unload1 v   (Left e stk)    = load e (Right v stk)
  \end{code}

  \pause
  \vspace*{-1.0em}
  \begin{code}
    load : Expr -> Stack -> ZipperType U+ Nat
    load (Val n)      stk = inj1 (n , stk)
    load (Add e1 e2)  stk = load e1 (Left e2 stk)
  \end{code}

}

\note{
  Purpose: First approximation rewrite |load| and |unload1|
  \begin{itemize}
      \item Now they are structurally recursive
      \item However they no longer compute eval
      \item Aside configuration: Relation between abstract machines and
        tail-recursive functions
  \end{itemize}
}


\frame{
  \frametitle{A tail-recursive evaluator}
  \begin{itemize}[<+->]
    \item Iterate |unload1| until a value is returned
      \begin{code}
        tail-rec-eval : Expr -> Nat
        tail-rec-eval e with load e Top
          ... | inj1 (n , stk)  = rec (n , stk)
          where
            nrec : ZipperType -> Nat
            rec (n , stk) with unload1 n stk
            ... | inj1 (n' , stk' )  = nrec (n' , stk')
            ... | inj2 r             = r
      \end{code}
    \item |(n' , stk')| \textbf{is not} structurally smaller than |(n , stk)|
  \end{itemize}
}

\note{
  Purpose: Show a first tail-recursive evaluator
  \begin{itemize}
      \item Still not accepted by termination checker
      \item But good as a starting point
  \end{itemize}
}


\frame{
  \frametitle{A tail-recursive evaluator (2)}
  \begin{itemize}[<+->]
    \item Using \textbf{well-founded} recursion
      \begin{code}
      tail-rec-eval : Expr -> Nat
      tail-rec-eval e with load e Top
        ... | inj1 (n , stk)  = rec (n , stk) ??1
        where
          rec : (z : ZipperType) -> Acc ltOp z -> Nat
          rec (n , stk) (acc rs) with unload1 n stk
          ... | inj1 (n' , stk')  = rec (n' , stk') (rs ??2)
          ... | inj2 r            = r
      \end{code}
    \item[] |ltOp : ZipperType -> ZipperType -> Set|
    \item[] |??1 : Acc ltOp (n , stk)|
    \item[] |??2 : (n' , stk') < (n , stk)|
  \end{itemize}

}

\frame{
  \frametitle{Invariant preserving configurations}
  \begin{itemize}[<+->]
    \item The |ZipperType| type is \textbf{too} liberal
    \item |x : ZipperType| and |y : ZipperType| might denote states 
          of the evaluation over \underline{different} |Expr|
    \item We can use dependent types to \textit{statically} \textbf{enforce} the
      invariant
  \end{itemize}
}

\frame{
  \frametitle{Invariant preserving configurations (2)}
  \begin{center}
    \input{figures/figure4}
  \end{center}
}

\frame{
  \frametitle{Invariant preserving configurations (3)}
    \begin{itemize}[<+->]
      \item Modify the \textbf{stack} to remember subexpressions
        \begin{code}
          data Stack2 : Set where
            Left    : Expr -> Stack2 -> Stack2
            Right   : (n : Nat) -> (e : Expr) -> eval e == n 
                    -> Stack2 -> Stack2
            Top     : Stack2
        \end{code}

    \item Recover the \textbf{input} expression
      \begin{code}
        plugup : Expr -> Stack2 -> Expr
        plugup e Top                 = e
        plugup e (Left t       stk)  = plugup (Add e t) stk
        plugup e (Right _ t _  stk)  = plugup (Add t e) stk


        data Zipperup (e : Expr) : Set where
          prodOp : (z : ZipperType) -> plugZup z == e -> Zipperup e
      \end{code}
  \end{itemize}
}

\frame{
  \frametitle{Well-founded |Expr| traversal}
  \begin{itemize}[<+->]
    \item |load| and |unload1| traverse the |Expr| left to right
    \item Each |ZipperType expr1| denotes a \underline{leaf} of the input expression
  \end{itemize}
  \pause[\thebeamerpauses]
  \begin{center}
  \input{figures/figure3}
  \end{center}
}


\frame{
  \frametitle{Up and down configurations}

    \input{figures/figure5}
    \flushright
    \vspace*{-1.0em}
    \input{figures/figure6}
}

\frame{
  \frametitle{Up and down configurations (2)}
  \begin{itemize}[<+->]
    \item A \textbf{reversed} view of the stack
      \begin{code}
        plugdown : Expr -> Stack2 -> Expr
        plugdown e Top                 = e
        plugdown e (Left t       stk)  = Add (plugdown e stk) t
        plugdown e (Right _ t _  stk)  = Add t (plugdown e stk)
      \end{code}

    \item \textbf{Top-down} type-indexed configurations
    \begin{code}
      data Zipperdown (e : Expr) : Set where
        prodOp : (z : ZipperType) -> plugZdown z == e -> Zipperdown e
    \end{code}
  \end{itemize}
}

\frame{
  \frametitle{Up and down configurations (3)}

  \begin{itemize}[<+->]
    \item Convert between views of the stack
      \begin{code}
        convert : ZipperType -> ZipperType
        convert (n , s) = (n , reverse s)

        plugdown-to-plugup  : forall (z : ZipperType)
                            -> plugZdown z ==  plugZup (convert z)
      \end{code}
    \item Invariant preserving conversion
      \begin{code}
      Zipperdown-to-Zipperup : (e : Expr) -> Zipperdown e -> Zipperup e

      Zipperup-to-Zipperdown : (e : Expr) -> Zipperup e -> Zipperdown e
      \end{code}
  \end{itemize}
}


\frame{
  \frametitle{Ordering configurations}

  \begin{itemize}
    \item We use |Zipperup| to \textbf{compute}
    \item We use |Zipperdown| to prove \textbf{termination}
  \end{itemize}

  \pause

  \begin{code}
    data IxLtOp : (e : Expr) -> Zipperdown e -> Zipperdown e -> Set where
      <-StepR  : llcorner r lrcorner ((t1 , s1) , ...) < ((t2 , s2) , ...)
        ->  llcorner Add l r lrcorner ((t1 , Right l n eq s1) , eq1) < ((t2 , Right l n eq s2) , eq2)
      <-StepL  : llcorner l lrcorner ((t1 , s1) , ...) < ((t2 , s2) , ...)
        ->  llcorner Add l r lrcorner ((t1 , Left r s1) , eq1) < ((t2 , Left r s2) , eq2)

      <-Base  :   (eq1 : Add e1 e2 == Add e1 (plugZdown t1 s1)) 
        ->        (eq2 : Add e1 e2 == Add (plugZdown t2 s2) e2)
        ->  llcorner Add e1 e2 lrcorner 
                  ((t1 , Right n e1 eq s1) , eq1) < ((t2 , Left e2 s2) , eq2)
  \end{code}
}

\frame{
  \frametitle{Ordering configurations (2)}
    \begin{itemize}
      \item The relation is \textbf{well-founded}
      \begin{code}
          <-WF : forall (e : Expr) -> Well-founded (llcorner e lrcornerLtOp)
          <-WF e x = acc (aux e x)
                where
                  aux : forall (e : Expr)  (x y : Zipperdown e)
                      -> llcorner e lrcorner y < x -> Acc (llcorner e lrcornerLtOp) y
                  aux = ...
      \end{code}
      \pause
      \item Indexing the relation by |e| is \textbf{necessary} for the proof!
    \end{itemize}
}

\frame{
  \frametitle{Completing the evaluator}
  \begin{itemize}[<+->]
      \item Invariant preserving |step|
        \begin{code}
          step : (e : Expr) -> Zipperup e -> Zipperup e U+ Nat
          step e ((n , stk) , eq)
            with unload n (Val n) refl stk
            ... | inj1 (n' , stk')  = inj1 ((n' , stk' ) , ...)
            ... | inj2 v            = inj2 v
        \end{code}
      \item |step| delivers a \textbf{smaller} configuration
        \begin{code}
          step-<  : forall (e : Expr) -> (z z' : Zipperup e) 
                  -> step e z == inj1 z'
                  -> llcorner e lrcorner Zipperup-to-Zipperdown z' < Zipperup-to-Zipperdown z
        \end{code}
  \end{itemize}
}

\frame{
  \frametitle{A terminating tail-recursive evaluator}
  \begin{itemize}[<+->]
      \item Auxiliary recursor
        \begin{code}
          rec  : (e : Expr) -> (z : Zipperup e)
              -> Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z) 
              -> Zipperup e U+ Nat
          rec e z (acc rs) = with step e z | inspect (step e) z
          ...  | inj2 n  | _       = inj2 n
          ...  | inj1 z' | [ Is ]
              = rec e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is))
        \end{code}
    \item Tail-recursive evaluator
        \begin{code}
          tail-rec-eval : Expr -> Nat
          tail-rec-eval e with load e Top
          ... | inj1 z = rec e (z , ...) (<-WF e z)
        \end{code}
  \end{itemize}
}

\frame{
  \frametitle{Correctness}
  \begin{itemize}[<+->]
    \item |rec| is correct by induction over |Acc|
    \begin{code}
      rec-correct  : forall (e : Expr) -> (z : Zipperup e)
                  -> (ac : Acc (llcorner e lrcornerLtOp) (Zipperup-to-Zipperdown z))
                  -> eval e == rec e z ac
      rec-correct e z (acc rs)
        with step e z | inspect (step e) z
      ...  | inj1 z'  | [ Is ]
          = rec-correct e z' (rs (Zipperup-to-Zipperdown z') (step-< e z z' Is))
      ...  | inj2 n   | [ Is ] = step-correct e z n Is
    \end{code}
    \item |tail-rec-eval| is correct
      \begin{code}
        correctness : forall (e : Expr) -> eval e == tail-rec-eval e
      \end{code}
  \end{itemize}
}

%} end of part1

\section{A generic tail-recursive evaluator}
%{ beginning of part2
%include part2.fmt


\frame{
  \frametitle{\textbf{regular}: \AD{Universe} + \AF{Interpretation}}

\begin{minipage}[c]{0.5\textwidth}
\begin{code}
  data Reg : Set1 where
    Zero  : Reg
    One   : Reg
    I     : Reg
    K     : (A : Set) -> Reg
    O+Op  : (R Q : Reg)  -> Reg
    O*Op  : (R Q : Reg) -> Reg
\end{code}
\end{minipage}
\pause
\begin{minipage}[c]{0.4\textwidth}
\begin{code}
  interp : Reg -> Set -> Set
  interpl Zero interpr X       = Bot
  interpl One interpr X        = Top
  interpl I interpr X          = X
  interpl (K A) interpr X      = A
  interpl (R O+ Q) interpr X   = interpl R interpr X U+ interpl Q interpr X
  interpl (R O* Q) interpr X   = interpl R interpr X * interpl Q interpr X
\end{code}
\end{minipage}

\pause
\begin{itemize}
  \item Values of type |interpl R interpr X| are functors over |X|
  \begin{code}
    fmap : (R : Reg) -> (X -> Y) -> interpl R interpr X -> interpl R interpr Y
  \end{code}
\end{itemize}
}

\frame{
  \frametitle{\textbf{regular}: \AD{Universe} + \AF{Interpretation} (2)}
  \begin{itemize}[<+->]
      \item Fixed point
        \begin{code}
          data mu (R : Reg) : Set where
            In : interpl R interpr (mu R) -> mu R
        \end{code}
      \item Fold (catamorphism)
        \begin{code}
          cata : (R : Reg) -> (interpl R interpr X -> X) -> mu R -> X
          cata R alg (In r) = alg (fmap R (cata R alg) r)
        \end{code}
  \end{itemize}
}

\frame{
  \frametitle{\textbf{regular}: Example}
  \begin{minipage}[c]{0,35\textwidth}
    \begin{code}
      expr : Reg
      expr = K Nat O+ (I O* I)

      ExprG : Set
      ExprG = mu expr
    \end{code}
  \end{minipage}
  \pause
  \begin{minipage}[c]{0,4\textwidth}
    \begin{code}
      from : Expr -> ExprG
      from (Val n) = inj1 n
      from (Add e1 e2) = inj2 (from e1 , from e2)

      to : ExprG -> Expr
      to (inj1 n)          = Val n
      to (inj2 (e1 , e2))  = Add (to e1) (to e2)
    \end{code}
  \end{minipage}
  \pause
  \begin{code}
  eval : ExprG -> Nat
  eval = cata expr phi
    where  phi : interpl expr interpr Nat -> Nat
           phi (inj1 n)         = n         
           phi (inj2 (n , n'))  = n + n'
  \end{code}
}

\frame{
  \frametitle{Dissection}
  \begin{itemize}[<+->]
      \item Another interpretation: codes |->| bifunctors
        \begin{code}
          nabla : (R : Reg) -> (Set -> Set -> Set)
          nabla Zero      X Y  = Bot
          nabla One       X Y  = Bot
          nabla I         X Y  = Top
          nabla (K A)     X Y  = Bot
          nabla (R O+ Q)  X Y  = nabla R X Y U+ nabla Q X Y
          nabla (R O* Q)  X Y   =            (nabla R X Y           * interpl Q interpr Y   ) U+  (interpl R interpr X   * nabla Q X Y           )
        \end{code}
  \item [Example:] |nabla (K Nat O+ (I O* I)) X Y|
    % \setlength{\itemindent}{2em}
      \begin{itemize}
        \item[=] |nabla (K Nat) X Y U+ nabla (I O* I) X Y|
        \item[=] |(nabla I X Y * interpl I interpr Y) U+ (interpl I interpr X * nabla I X Y)|
        \item[=] |(Top * Y) U+ (X * Top)|
        \item[=] |Y U+ X|
      \end{itemize}
\end{itemize}
}

\frame{
  \frametitle{Generic stacks}

  \begin{itemize}[<+->]
      \itemsep-0.75em
      \item Store trees, values and proofs
        \begin{code}
        record Computed (R : Reg) (X : Set)  (alg : interpl R interpr X -> X) 
                                             : Set where
            constructor _,_,_
            field
              Tree   : mu R
              Value  : X
              Proof  : catamorphism R alg Tree == Value

      \end{code}

      \item |Computed| to the left; trees to the right
        \begin{code}
          Stack  : (R : Reg) -> (X : Set) 
                 -> (alg : interpl R interpr X -> X) -> Set
          Stack R X alg = List (nabla R (Computed R X alg) (mu R))
        \end{code}
      \item[Example:]
        \begin{code}
          Stack (K Nat O+ (I O* I)) Nat phi  
            =  List (Computed (K Nat O+ (I O* I)) phi U+ mu (K Nat O+ (I O* I)))
            ~=  Stack2
        \end{code}
  \end{itemize}
}

\frame{
  \frametitle{Generic plug}
  \begin{itemize}[<+->]
    \item Plug a \textit{single} layer
      \begin{code}
      plug : (R : Reg) -> (X -> Y) -> R X Y * Y -> interpl R interpr Y
      \end{code}
    \item Plug through the \textit{stack}
      \begin{code}
      plug-mudown  : (R : Reg) -> {alg : interpl R interpr X -> X}
                   -> mu R -> Stack R X alg -> mu R
      plug-mudown R t []         = t
      plug-mudown R t (h :: hs)  
          = In (plug R Computed.Tree h (plug-mudown R t hs))


      plug-muup  : (R : Reg) -> {alg : interpl R interpr X -> X}
                 -> mu R -> Stack R X alg -> mu R
      plug-muup R t []         = t
      plug-muup R t (h :: hs)  
          = plug-muup R (In (plug R Computed.Tree h t)) hs
    \end{code}
  \end{itemize}
}

\frame{
  \frametitle{Generic leaves}
  {\large There are two levels of \textbf{recursion} in a generic tree}
  \pause
  \begin{itemize}[<+->]
      \item Functor: composition of functors |R O* Q|
      \item Fixed point: |interpl R interpr (mu R)|
  \end{itemize}

  \pause[\thebeamerpauses]
  \begin{code}
    data NonRec : (R : Reg) -> interpl R interpr X -> Set where
      NonRec-One  : NonRec One tt
      NonRec-K    : (B : Set) -> (b : B) -> NonRec (K B) b
      NonRec-+1   : (R Q : Reg) -> (r : interpl R interpr X)
                  -> NonRec R r -> NonRec (R O+ Q) (inj1 r)
      NonRec-+2   : ...
      NonRec-*    : ...
  \end{code}

  \pause
  \vspace*{-0.5em}
  {\large \emph{Example:}} \\
  \begin{code}
  Val-NonRec : forall (n : Nat) -> NonRec (K Nat O+ (I O* I)) (inj1 n)
  Val-NonRec : n = NonRec-+1 (K Nat) (I O* I) n (NonRec-K Nat n)
  \end{code}
}

\frame{
  \frametitle{Generic configurations}

  \begin{itemize}[<+->]
    \setlength{\itemindent}{-1em}
    \item Generic configuration = \textbf{leaf} + \textbf{stack}
      \begin{code}
        Zipper  : (R : Reg) -> (X : Set) 
                -> (alg : interpl R interpr X -> X) -> Set
        Zipper R X alg = Sigma (interpl R interpr X) (NonRec R) * Stack R X alg
      \end{code}

    \item \textit{Embed} a leaf into a generic tree
      \begin{code}
      coerce : (R : Reg) -> (x : interpl R interpr X) -> NonRec R x -> interpl R interpr Y  
      \end{code}

    \item Recover the \textbf{input} tree
      \begin{code}
        plugZ-mudown  : (R : Reg) {alg : interpl R interpr X -> X} 
                      -> Zipper R X alg -> mu R ->  Set
        plugZ-mudown R ((l , isl) , s) t = plug-mudown R (In (coerce l isl)) s t
      \end{code}
  \end{itemize}
}

\frame{
  \frametitle{One step of a catamorphism}

  {\large Generic |unload|}
  \pause
  \begin{code}
    unload : (R : Reg) -> (alg : interpl R interpr X -> X)
          -> (t : mu R) -> (x : X) -> catamorphism R alg t == x
          -> Stack R X alg -> Zipper R X alg U+ X
    unload R alg t x eq []        = inj2 x
    unload R alg t x eq (h :: hs) with right R h (t , x , eq)
    unload R alg t x eq (h :: hs) | inj1 r with compute R r
    ... | (rx , rr) , eq'   = unload R alg (In rp) (alg rx) eq' hs
    unload R alg t x eq (h :: hs) | inj2 (dr , q) 
                            = load R q (dr :: hs)
  \end{code}

  \pause
  \vspace*{-1.25em}
  \begin{code}
    right  : (R : Reg) -> nabla R X Y -> X -> interpl R interpr X U+ (nabla R X Y * Y)
  \end{code}

  \pause
  \vspace*{-1.25em}
  \begin{code}
    compute : (R : Reg) {alg : interpl R interpr X -> X}
        -> interpl R interpr (Computed R X alg)
        -> Sigma (interpl R interpr X * interpl R interpr (mu R)) lambda { (r , t) -> cata R alg (In t) == alg r }
  \end{code}

}
\frame{
  \frametitle{A well-founded generic relation}
  {\large The \underline{two} levels of recursion induce \underline{two} relations}
  \only<2>{
    \begin{itemize}
      \item Functor
      \begin{code}
        data <NablaOp  : (R : Reg) 
                      -> nabla R X Y * Y -> nabla R X Y * Y -> Set where
          step-+1  :  llcorner  R lrcorner      (r , t1)       <Nabla    (r' , t2)
                  ->  llcorner R O+ Q lrcorner  (inj1 r , t1)  <Nabla (inj1 r' , t2)

          step-+2  : ...

          step-*1  :   llcorner R lrcorner       (dr , t1)             <Nabla (dr' , t2)
                  ->  llcorner R O* Q lrcorner  (inj1 (dr , q) , t1)  <Nabla (inj1 (dr' , q) , t2)

          step-*2  : ...

          base-*   :   llcorner R O* Q lrcorner (inj2 (r , dq) , t1)   <Nabla  (inj1 (dr , q) , t2)
      \end{code}
    \end{itemize}
    }
    \only<3>{
      \begin{itemize}
      \item Fixed point
        \begin{code}
          data <ZOp : Zipper R X alg -> Zipper R X alg -> Set where
            Step   :  (t1 , s1) <Z (t2 ,  s2) 
                  -> (t1 , h :: s1) <Z (t2 , h  :: s2)

            Base  :   plugZ-mudown R (t1 , s1) == e1 
                  ->  plugZ-mudown R (t2 , s2) == e2
                  -> (h1 , e1) <Nabla (h2 , e2) 
                  -> (t1 , h1 :: s1) <Z (t2 , h2 :: s2)
        \end{code}
    \end{itemize}
    }
}

\frame{
  \frametitle{A well-founded generic relation (2)}
  \begin{itemize}[<+->]
    \item Type-indexed relation over |Zipperdown|
      \begin{code}
        data IxLtdown {X : Set} (R : Reg) {alg : interpl R interpr X -> X}  
                : (t : mu R) 
                -> Zipperdown R X alg t -> Zipperdown R X alg t -> Set where
      \end{code}

    \item The relation is \textbf{well-founded}
      \begin{code}
        <Z-WF : forall (R : Reg)  -> (t : mu R) 
              -> Well-founded (llcorner R lrcornerllcorner t lrcornerIxLtdown)
      \end{code}
  \end{itemize}
}

\frame{
  \frametitle{Invariant preserving step}
  \begin{itemize}[<+->]
    \item One step of the catamorphism
      \begin{code}
        step  : (R : Reg) -> (alg : interpl R interpr X -> X) -> (t : mu R)
              -> Zipperup R X alg t -> Zipperup R X alg t U+ X
      \end{code}
    \item |step| delivers a \textbf{smaller} configuration
      \begin{code}
        step-<  : (R : Reg) (alg : interpl R interpr X -> X) -> (t : mu R)
                -> (z1 z2 : Zipperup R X alg t)
                -> step R alg t z1 == inj1 z2 -> llcorner R lrcornerllcorner t lrcorner z2 <ZOp z1
      \end{code}
  \end{itemize}
}

\frame{
  \frametitle{A generic tail-recursive evaluator}
  \begin{itemize}[<+->]
      \item Auxiliary recursor
      \begin{code}
        rec  : (R : Reg) (alg : interpl R interpr X -> X) (t : mu R) 
            -> (z : Zipperup R X alg t) 
            -> Acc (llcorner R lrcornerllcorner t lrcornerIxLtdown ) (Zipperup-to-Zipperdown z) -> X
        rec R alg t z (acc rs) with step R alg t z | inspect (step R alg t) z
        ... | inj1 x |  [ Is  ] = rec R alg t x (rs x (step-< R alg t z x Is))
        ... | inj2 y |  [ _   ] = y
      \end{code}
      \item Tail-recursive evaluator
      \begin{code}
        tail-rec-cata : (R : Reg) -> (alg : interpl R interpr X -> X) -> mu R -> X
        tail-rec-cata R alg x  with load R alg x []
        ... | inj1 z = rec R alg (z , ...) (<Z-WF R z)
      \end{code}
  \end{itemize}
}
    
\frame{
  \frametitle{Correctness, generically}
  \begin{itemize}[<+->]
    \item The correctness proof follows the same pattern as in |tail-rec-eval|
    \item Induction over |Acc| and an auxiliary lemma |step-correct|
  \end{itemize}
  \pause[\thebeamerpauses]
  \begin{code}
    correctness  : forall (R : Reg) (alg : interpl R interpr X -> X) (t : mu R)
                 -> catamorphism R alg t == tail-rec-cata R alg t
  \end{code}

}

\section{Discussion}

\frame{
  \frametitle{Discussion}
  \begin{itemize}[<+->]
      \item Runtime impact of storing proofs and subtrees
      \item Regular universe is limited
      \item Directly executable machine in comparison with other techniques
  \end{itemize}
}

\section{Conclusions}

\frame{
  \frametitle{Conclusions}
  \begin{itemize}[<+->]
    \item We have developed a \textbf{tail-recursive} evaluator for |Expr|
    \item We generalized it for any algebra over any \textbf{regular} datatype
    \item We proved the evaluators to be \textbf{terminating} and \textbf{correct}
  \end{itemize}
}

\frame{
  \frametitle{Future work}
  \begin{itemize}[<+->]
    \item More expressive universes
    \item Other theorem provers
    \item Long-term goal: abstract machine for |lambda|-calculus
  \end{itemize}
}

%} end of part2
\frame{

  \centering
  {\Large Thank you very much for your attention!}
}

\end{document}
