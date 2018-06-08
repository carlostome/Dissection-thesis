\documentclass[a4paper]{book}
\usepackage[top=1in, bottom=1.25in, left=1.70in, right=1.70in]{geometry}

\usepackage[english]{babel}
% \usepackage{gfsdidot}
\usepackage{lmodern}
% \usepackage[firstpage]{draftwatermark}

\usepackage{graphicx}
\usepackage{hyperref}
\usepackage[draft]{todonotes}
% \usepackage[disable]{todonotes}
\usepackage{xcolor}
\usepackage[framemethod=TikZ]{mdframed}
% \usepackage{showframe}
% \usepackage{multirow}
\usepackage{alltt}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}

\usepackage{cleveref}

\usepackage{ucs}
\usepackage[utf8x]{inputenc}

% \usepackage{apalike}
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

% Theorem styles
\newtheorem{theorem}{Theorem}[section]
\newtheorem{remark}{Remark}[section]
\newtheorem{conjecture}{Conjecture}[section]
\theoremstyle{definition}
% \newtheorem{example}{Example}[section]
% \newtheorem{examplex}{Example}[section]
% \newenvironment{example}
%   {\pushQED{\qed}\renewcommand{\qedsymbol}{$\triangle$}\examplex}
%   {\popQED\endexamplex}
\newtheorem{definition}{Definition}[section]

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
        frametitlebackgroundcolor=gray!30
    ]%
}{%
    \end{mdframed}
}


% find a solution for hspace -- crappy crappy--
\newcommand{\nonterm}[1]{\hspace*{-0.1cm}\colorbox{orange!25}{#1}}

\newcommand{\definedin}[1]{\footnote{Module: #1}}
\newcommand{\args}[1]{\overline{#1}}
\newcommand{\ttargs}[1]{\(\args{\texttt{#1}}\)}
\newcommand{\ttunderline}[1]{\(\underline{\texttt{#1}}\)}
\definecolor{ttemph1}{HTML}{BB0000}
\definecolor{ttemph2}{HTML}{0000BB}
% \newcommand{\ttemph}[2]{%
% \ifnum#1=1\textcolor{ttemph1}{\textbf{#2}}%
% \else\ifnum#1=2\textcolor{ttemph2}{\textbf{#2}}%
% \else\textbf{#2}%
% \fi\fi}
\newcommand{\codeemph}[2]{%
\ifnum#1=1\textcolor{ttemph1}{\textsf{\textbf{#2}}}%
\else\ifnum#1=2\textcolor{ttemph2}{\textsf{\textbf{#2}}}%
\else\textbf{#2}%
\fi\fi}

\newcommand{\Bool}{\textrm{Bool}}
\newcommand{\List}{\textrm{List}}
\newcommand{\Nat}{\textrm{Nat}} % or \mathit{N\!at}
\newcommand{\NatList}{\textrm{NatList}}
\newcommand{\PairOfBools}{\textrm{PairOfBools}}
\newcommand{\RoseTree}{\textrm{RoseTree}}
% \newcommand{\Tree}{\textrm{Tree}}

%--------------------------------------------------

%  Agda mess

\usepackage[conor]{agda}
% \usepackage{agda}
\usepackage{catchfilebetweentags}
\usepackage{autofe}

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

%% And a non-numbered variant
\newenvironment{agda*}{%
%\par\addvspace{1em}
\noindent%
\begin{samepage}%
\normalsize%
}{%
\end{samepage}%
\noindent%
%\par\addvspace{1em}%
}

\setlength\parindent{0pt}
%% Multiple columns of agda code.
%% Optional argument represents percentage of
%% \textwidth that the minipage will use.
\newenvironment{agdaCol}[1][0.49]{%
\begin{minipage}[t]{#1\textwidth}
}{%
\end{minipage}
}

%% standard vertical spacing
\newcommand{\stdvspace}{%
\par\addvspace{0.8em}
}
\newcommand{\InsertCodeInline}[2]{\codeinlinetrue\ExecuteMetaData[../src-tex/#1]{#2}}

\newcommand{\InsertCode}[2]
  { \begin{samepage}
    \ExecuteMetaData[../src-tex/#1]{#2}
    \end{samepage}
  }

\newcommand{\InsertCodeN}[2]{
  % \codeinlinefalse
  \medskip
  \ExecuteMetaData[../src-tex/#1]{#2}\refstepcounter{codeblock}\begin{center}Listing \thecodeblock\end{center}\label{code:#2}%

  \medskip}

\newcounter{codeblock}
\newcommand{\labelcodeblock}[2]{\refstepcounter{codeblock}\label{#1}\begin{center}Listing \thecodeblock\end{center}}

%---

\newcommand{\greyFG}[1]{\textcolor[rgb]{0.15,0.15,0.15}{#1}}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\D}[1]{\blueFG{\textsf{##1}}} % Types
  % \newcommand{\V}[1]{\blackFG{\textsf{#1}}} % Variables
  \newcommand{\V}[1]{\greyFG{\textsf{##1}}} % Variables
  % \newcommand{\K}[1]{\mathbf{#1}}
  % \newcommand{\K}[1]{\orange{\textsf{\textbf{#1}}}} % Keywords
  \newcommand{\K}[1]{\orangeFG{\textsf{##1}}} % Keywords
}
\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}
\ColourStuff

%--------------------------------------------------

\setmainfont[ItalicFont = xits-italic.otf
, BoldFont = xits-bold.otf
, BoldItalicFont = xits-bolditalic.otf]{xits-regular.otf}
\setmathfont[BoldFont = xits-mathbold.otf]{xits-math.otf}
\setsansfont[Scale=MatchLowercase
, ItalicFont = DejaVuSans-Oblique.ttf
, BoldFont = DejaVuSans-Bold.ttf
, BoldItalicFont = DejaVuSans-BoldOblique.ttf]{DejaVuSans.ttf}
\setmonofont[Scale=MatchLowercase
, ItalicFont = DejaVuSansMono-Oblique.ttf
, BoldFont = DejaVuSansMono-Bold.ttf
, BoldItalicFont = DejaVuSansMono-BoldOblique.ttf]{DejaVuSansMono.ttf}

\newfontfamily{\xitsfont}[Scale=MatchLowercase]{xits-regular.otf}

\DeclareTextFontCommand{\textxits}{\xitsfont}

\renewcommand{\familydefault}{\sfdefault}

\usepackage{newunicodechar}

\newunicodechar{∇}{\textxits{∇}}
\newunicodechar{μ}{\textxits{μ}}
\newunicodechar{φ}{\textxits{φ}}
\newunicodechar{ϕ}{\textxits{ϕ}}
% \newunicodechar{⌷}{\textxits{$\vrectangle$}}
% \newunicodechar{▱}{\textxits{\rotatebox[origin=c]{105}{▱}}}
\newunicodechar{⊎}{\textxits{⊎}}
% \newunicodechar{||}{\textxits{||}}

\newcommand{\Agda}{\emph{Agda}}

%--------------------------------------------------

\newcommand{\rewrite}[1]{\todo[color=blue!40,noline]{Rewrite}}
\newcommand{\arewesure}[1]{\todo[color=red!40,noline]{#1}}
\newcommand{\referenceneeded}[1]{\todo[color=green!40,noline]{#1}}
\newcommand{\colored}{\todo[color=pink!40,noline]{Color the stuff}}

\title{Verified tail recursive folds through dissection}
\date{\today}
\author{Carlos Tom\'e Corti\~nas}

\begin{document}

\maketitle

\begin{flushright}
\emph{Supervised by} Wouter Swierstra\\
\emph{Second supervisor} Alejandro Serrano Mena
\end{flushright}

\tableofcontents

% \listoftodos
\include{introduction}
\include{background}
% \include{expression}
% \include{generic}

\bibliographystyle{plain}
% \bibliographystyle{alpha}
% \bibliographystyle{apa}
\bibliography{main}

\end{document}
