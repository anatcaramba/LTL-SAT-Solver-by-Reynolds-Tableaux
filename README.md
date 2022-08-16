# An OCaml tableau solver for unary linear temporal logic

This program is an implementation in OCaml of the tableau satisfiability solver for the (X,F)-fragment of LTL given in ([Reynolds 2016](https://arxiv.org/abs/1604.03962)). 
It takes as input a formula, and returns `true` **and a model** if the formula is satisfiable, `false` if it is not. The solver also prints the development of the tree during model search.

A theoretical foundation for this solver is given by the *completeness* of the treated fragment of LTL with respect to the axiomatization, combined with the completeness of Reynolds' tableau procedure; see Theorem 3.3 in ([Ghilardi and van Gool 2017](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/div-classtitlea-model-theoretic-characterization-of-monadic-second-order-logic-on-infinite-wordsdiv/6B7E629B0B30B876618FC9EBF0AB9996)) and sections 7&8 in ([Reynolds 2016](https://arxiv.org/abs/1604.03962)) Concretely, these theorems ensure that the solver will always give an output. 

This solver was written in Summer 2022 by Anatole Leterrier in the context of an MPRI (M2) internship at [IRIF](https://www.irif.fr) under the supervision of [Sam van Gool](https://www.samvangool.net). The solver is accompanied by a technical [internship report](./report.pdf) that provides theoretical background. We gratefully acknowledge the financial support for the internship from the [DIM Maths Innov](https://www.dim-mathinnov.fr/) program of the [FSMP](https://sciencesmaths-paris.fr/) and the Île-de-France region. 

# Overview of the source code

(TODO complete this section)

(TODO make the source tree very simple and clean, so that it is easy for someone to navigate. Then update all the links in this file.)

(TODO Change the filenames into something more descriptive, for example func.ml -> solver.ml and test_prog.ml -> test_solver.ml)

The main program is in the file [filename](with link)

The tests are in the file [filename](with link)
# Dependencies

The program depends on the following software, which you need to install to be able to compile it on your own machine:

- ocaml version 4.13.1+
- opam version 2.1.2+
- dune version 3.3.1+
- ounit2 version 2.2.6+

(TODO add hyperlinks to the above items)
# Usage

To compile the program, while in the subfolder `tableaux`, execute the command `dune build` on a shell.

The current version of the program can be tested in two ways: 

1. By modifying the tests in the file `test_prog.ml`.

2. In an interactive toplevel such as `ocaml` or `utop`. To import the code, type:
` #use "./tableaux/test_prog/func.ml";; `

(TODO add a complete example of a phi)

You can now apply function "sat" on any LTL formula by typing:
` let _ = sat(phi) ;; `

We recall the syntax used for LTL formulas in this program:
* Propositional variables are written ` Prop 'p' `; that is, `Prop` is an operator taking a `char` as an argument);
* Binary operators for Conjunction and Disjunction: ` And(phi,psi) `, ` Or(phi,psi) ` ;
* Unary operators for Negation, Next, Finally, Globally: `Neg(phi)`, `X(phi)`, `F(phi)`, `G(phi)`.


# Tests

There are several tests in the file `./tableaux/test_prog.ml`. Many of these are unit tests, written during programming to ensure that the functions in `func.ml` were well written.

To execute all the tests, run the command

`dune exec tableaux/test_prog.exe`

We have created a sequence of formulas that exhibits the worst-case performance of the solver. It corresponds to the "exponential case" test. The formula in the test case only has 5 nested operators, however we have tested up to 13 nestings, by recursively taking the disjunction of twice the formula with n-1 nestings. Since the procedure is PSPACE-complete (TODO add reference), we would expect an exponential time in functions of the number of nestings in the worst case, which is what we seem to get. This is normal, as adding a nesting doubles the number of leaves. A table and a graph in the report mentioned earlier bring further evidence of this fact.  (TODO modify this to a precise reference to a section of your report)

# Known limitations

In case an eventuality subformula (F or G) is present and the program claims satisfiability with the "LOOP" rule, it will tell the user to loop to find the actual, infinite model (eg. `G(Prop 'p')`). The current version does not yet specify exactly where to loop; this point is left to future work. If the program does not end with the "LOOP" rule, an infinite model is found by choosing any valuation for the remaining states. It also happens that a propositional variable is present as a subformula, but not specified in the model. This means that the choice of the truth value for this variable is not relevant to the satisfiability of the formula (eg. `Or(Prop 'p',Prop 'q')` will simply tell to set variable `p` to true, and not specify a truth value for `q`).

The implementation can likely still be optimized for time and space performance, also see the discussion in Section x.y of the [report](./report.pdf) (TODO add precise reference).
