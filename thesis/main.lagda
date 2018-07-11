\documentclass[a4paper]{book}
\usepackage[pass]{geometry}
\usepackage[english]{babel}
\usepackage{lmodern}
\usepackage{graphicx}
\usepackage{hyperref}
\usepackage[draft]{todonotes}
\usepackage[framemethod=TikZ]{mdframed}
\usepackage{alltt}
\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{amssymb}
% \usepackage{mathspec}
\usepackage{bbold}      %% Font for fancy math letters

% \usepackage{geometry}
\usepackage{fancyhdr}
% \usepackage{xcolor}
\usepackage{titlesec}
% \usepackage{ccaption}
% \usepackage{tocloft}

\usepackage{scalerel}   %% Scale
\usepackage{dsfont}     %% Font for fancy math letters
\usepackage{cleveref}

\usepackage{ucs}
\usepackage[T1]{fontenc}
\usepackage[utf8x]{inputenc}
\usepackage{textcomp}
\usepackage{lmodern}
\renewcommand{\familydefault}{\sfdefault}
\usepackage{csquotes} %% Quotes

\usepackage{natbib}

\usepackage{tikz}
\usetikzlibrary{fit}
\usetikzlibrary{shapes}
\pgfdeclarelayer{background}
\pgfdeclarelayer{foreground}
\pgfsetlayers{background,main,foreground}
\usetikzlibrary{decorations.pathreplacing,calc}

%% TikZ
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

%include main.fmt

% Frame color
\definecolor{shadecolor}{rgb}{1.0,0.9,0.7}

%% Example frames
\newcounter{example}[section]

\renewcommand{\theexample}{\thesection.\arabic{example}}

\newenvironment{example}[1][]{%
    \refstepcounter{example}
    \begin{mdframed}[%
        frametitle={Example \theexample\ #1},
        skipabove=\baselineskip plus 2pt minus 1pt,
        skipbelow=\baselineskip plus 2pt minus 1pt,
        linewidth=0.5pt,
        frametitlerule=true,
        frametitlebackgroundcolor=gray!20,
        rightline=false,
        leftline=false
    ]\medskip
}{%
    \medskip
    \end{mdframed}
    \medskip
}


% find a solution for hspace -- crappy crappy--
\newcommand{\nonterm}[1]{\hspace*{-0.1cm}\colorbox{orange!25}{#1}}
\newcommand{\hole}[1]{\colorbox{yellow!50}{\ensuremath{\bigbox_{#1}}}}

%--------------------------------------------------

%  Agda mess

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

%--------------------------------------------------

\newcommand{\Agda}{\emph{Agda}}
\newcommand{\Haskell}{\emph{Haskell}}

\renewcommand\hscodestyle{%
   \setlength\leftskip{1.25em}%
}

\bibpunct{[}{]}{,}{a}{}{;}
%--------------------------------------------------

\setcounter{tocdepth}{1} % Show only up to sections in ToC

%-------------------------------------------------
% Title page take from https://github.com/VictorCMiraldo/latex-uustthesis

\newcommand{\HRule}{\rule{\linewidth}{0.5mm}} % Defines a new command for horizontal lines, change thickness here
% %% Declare a supervisor variable for our title page.
% % \let\@@supervisor\@@empty
% \newcommand{\supervisor}[1]{\gdef\@@supervisor{#1}}

%\renewcommand{\maketitle}{
%\thispagestyle{empty}
%\begin{center}
%%%%%%%%%%%%%%
%%% Headings
%  \begin{minipage}{0.25\textwidth}%
%  \includegraphics[width=.8\textwidth]{img/logo.pdf}%
%  \end{minipage}
%  ~
%  \begin{minipage}{0.7\textwidth}%
%  \begin{flushleft}
%  \textsc{\huge Universiteit Utrecht}\vskip 1.5em
%  \textsc{\Large Faculty of Science}\vskip 0.5em
%  \textsc{\large Dept. of Information and Computing Sciences}%
%  \end{flushleft}
%  \end{minipage}
%%%%%%%%%%%%
%%% Title
%  \vfill
%  \HRule\vskip 1.5em
%  {\huge\bfseries \@@title }
%  \vskip 1em \HRule
%  \vfill
%%%%%%%%%%
%% Author(s)
  %\begin{minipage}{0.4\textwidth}
  %  \begin{flushleft}\large
  %  \textit{Author}\vskip .5em
  %  \@@author
  %  \end{flushleft}
  %\end{minipage}
  %~
  %\begin{minipage}{0.4\textwidth}
  %\begin{flushright}\large
  %\textit{Supervisor}\vskip .5em
  %\@@supervisor
  %\end{flushright}
  %\end{minipage}
  %\vfill\vfill\vfill
%%%%%%%%%%%%%
%%%% Date
 % {\large\@@date} 
 % \vfill\newpage
% \end{center}
% }

\titleformat{\chapter}[block]%
{\bfseries\Large\filleft}%
{\Huge\color{gray}\thechapter}%
{1em}
{\hfill\Huge\scshape}%
[\HRule]

\title{Verified tail-recursive folds through dissection}
\date{\today}
\author{Carlos Tom\'e Corti\~nas}

\begin{document}

\newgeometry{hmarginratio=1:1} %% Change geometry for titlepage
\begin{titlepage}
  \vspace*{3em}
  \centering
  \includegraphics[width=.8\textwidth]{img/UU_logo_NL_RGB.jpg}%

  {\Large{Master Thesis in Computing Science}}

  \vspace*{3em}
  {\huge\bfseries Verified tail-recursive folds\\ through dissection}
  \vspace*{3em}

  {\LARGE{Carlos Tomé Cortiñas}}

  
\end{titlepage}
\restoregeometry

\thispagestyle{empty}
\section*{Abstract}

The functional programming paradigm advocates a style of programming based on
higher-order functions over inductively defined datatypes. A fold, which
captures their common pattern of recursion, is the prototypical example of such
a function. However, its use comes at a price. 

The definition of a fold is not tail-recursive which means that the size of the
stack during execution grows proportionally to the size of the input.
\cite{McBride:2008:CLM:1328438.1328474} has proposed a method called
\emph{dissection}, to transform a fold into its tail-recursive counterpart.
Nevertheless, it is not clear why the resulting function terminates, nor it is
clear that the transformation preserves the fold's semantics.

In this thesis, we formalize the construction of such tail-recursive function
and prove that it is both terminating and equivalent to the fold. In addition,
using \citeauthor{McBride:2008:CLM:1328438.1328474}'s dissection, we generalize
the tail-recursive function to work on any algebra over any regular datatype.

\newpage
\thispagestyle{empty}
\section*{Acknowledgements}
\todo{say something nice}

\tableofcontents

% \listoftodos
\input{introduction}
\input{background}
\input{expression}
\input{generic}
\input{conclusion}

\bibliographystyle{plainnat}
\bibliography{main}

\end{document}

