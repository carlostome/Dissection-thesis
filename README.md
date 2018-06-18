# Dissection-thesis
This repository contains the source files, Agda and LaTeX for my MSc thesis.

The formalization in _Agda_ is stored under the directory `src/Thesis/`, the modules are organized as follows:
- `src/Thesis/Data` contains auxiliary definitions about common types such as List, Sum, Either, etc
- `src/Thesis/Tree/Indexed.agda` contains the formalization of the tail-recursive fold for the type of binary trees. The other two files inside the same folder are slight variations of it.
- `src/Thesis/Regular.agda` contains the formalization of the tail-recursive catamoprhism for the regular universe. It depends on the following modules:
  + `src/Thesis/Regular/Core.agda`: Definition of the _regular_ universe.
  + `src/Thesis/Regular/Catamorphism.agda`: Definition of catamorphism and auxiliary relations.
  + `src/Thesis/Regular/Dissection.agda`: Definition of _dissection_ and relation over _dissections_.
  + `src/Thesis/Regular/Equality.agda`: Heterogeneous equality of values in the regular universe.
  + `src/Thesis/Regular/Right.agda` : Definition of the function _right_ and ancillary relations.
  + `src/Thesis/Regular/First.agda` : Function _first_ and auxiliary definitions. 
  + `src/Thesis/Regular/Last.agda` : Predicate about the last _hole_ of a dissection.
  + `src/Thesis/Dissection/Core.agda` : Core definitions of the tail-recursive catamorphism such as Zipper (in the paper named Configuration), Stack, Computed, etc.
  + `src/Thesis/Dissection/Load.agda` : Function _load_ and related properties.
  + `src/Thesis/Dissection/Relation.agda` : Relation over generic Zipper (Configurations in the paper) and the proof of well-foundedness.

The code typechecks in Agda version 2.5.3 and standard library version 0.14
