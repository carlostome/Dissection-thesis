# Dissection-thesis
This repository contains the source files, Agda and LaTeX for my MSc thesis.

## Abstract
> The functional programming paradigm advocates a style of programming based on higher-order functions over inductively defined datatypes. A fold, which captures their common pattern of recursion, is the prototypical example of such a function. However, its use comes at a price. The definition of a fold is not tail-recursive which means that the size of the stack during execution grows proportionally to the size of the input. McBride has proposed a method called *dissection*, to transform a fold into its tail-recursive counterpart. Nevertheless, it is not clear why the resulting function terminates, nor it is clear that the transformation preserves the fold's semantics.

> In this thesis, we formalize the construction of such tail-recursive function and prove that it is both terminating and equivalent to the fold. In addition, using McBride's dissection, we generalize the tail-recursive function to work on any algebra over any regular datatype.

## Source files
There are three main folders in the repository:
- `thesis`: Files for building the thesis document
- `paper` : Files for building the accompanying paper
- `presentation`: Files for the thesis defense presentation
- `src`: Formalization in _Agda_
  The Agda module structure is the following:
    + `src/Data` contains auxiliary definitions about common types such as List, Sum, Either, etc
    + `src/Tree/Indexed.agda` contains the formalization of the tail-recursive fold for the type of binary trees. The other two files inside the same folder are slight variations of it.
    + `src/Regular.agda` contains the formalization of the tail-recursive catamoprhism for the regular universe. It depends on the following modules:
      - `src/Regular/Core.agda`         : Definition of the _regular_ universe.
      - `src/Regular/Catamorphism.agda` : Definition of catamorphism and auxiliary relations.
      - `src/Regular/Dissection.agda`   : Definition of _dissection_ and relation over _dissections_.
      - `src/Regular/Equality.agda`     : Heterogeneous equality of values in the regular universe.
      - `src/Regular/Right.agda`        : Definition of the function _right_ and ancillary relations.
      - `src/Regular/First.agda`        : Function _first_ and auxiliary definitions. 
      - `src/Regular/Last.agda`         : Predicate about the last _hole_ of a dissection.
      - `src/Dissection/Core.agda`      : Core definitions of the tail-recursive catamorphism such as Zipper (in the paper named Configuration), Stack, Computed, etc.
      - `src/Dissection/Load.agda`      : Function _load_ and related properties.
      - `src/Dissection/Relation.agda`  : Relation over generic Zipper (Configurations in the paper) and the proof of well-foundedness.

The code typechecks in _Agda_ version 2.5.3 and standard library version 0.14

## Build

There is a shake
