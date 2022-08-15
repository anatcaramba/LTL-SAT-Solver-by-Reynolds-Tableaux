# An OCaml tableau solver for LTL

This program is an implementation of [Reynolds](https://arxiv.org/abs/1604.03962). It takes as input an LTL formula.
It prints the development of the tree while searching for a model.
It returns `true` **and a model** if the formula is satisfiable, `false` if it is not.

In case an eventuality subformula (F or G) is present and the program claims satisfiability with the "LOOP" rule, it will tell the user to loop to find the actual, infinite model (eg. `G(Prop 'p')`). From where to loop is left to the user, sadly. If the program does not end with the "LOOP" rule, an infinite model is found by choosing any valuation for the remaining states. It also happens that a propositional variable is present as a subformula, but not specified in the model. This means that the choice of the truth value for this variable is not relevant to the satisfiability of the formula (eg. `Or(Prop 'p',Prop 'q')` will simply tell to set variable `p` to true).


We recall the syntax used for LTL formulas in this program:
Propositional variables are written ` Prop 'p' ` (Prop is an operator taking a char as an argument);
Then, binary operators for Conjunction and Disjunction: ` And(phi,psi) `, ` Or(phi,psi) ` ;
Unary operators for Negation, Next, Finally, Globally: `Neg(phi)`, `X(phi)`, `F(phi)`, `G(phi)`.

# Usage

To compile the program, go into repository "tableaux":

`cd tableaux`

and execute the command:

`dune build`

on a shell.


To run the program on a formula of your choice, run the toplevel (command `ocaml`). Then type:
` #use "./tableaux/test_prog/func.ml";; `

You can now apply function "sat" on any LTL formula by typing:
` let _ = sat(phi) ;; `



Since the procedure is complete (for a proof, see for example [this report](./report.pdf)), the solver will always give an output. 

We have not yet made time performance optimizations.

# Tests

There are several tests in the subfolder, many of which were written during programming to ensure that the functions in "func.ml" were well written.

To execute all the tests, run the command

`dune exec tableaux/test_prog.exe`

We have created a sequence of formulas that exhibits the worst-case performance of the solver. It corresponds to the "exponential case" test. The formula in the test case only has 5 nested operators, however we have tested up to 13 nestings, by recursively taking the disjunction of twice the formula with n-1 nestings. Since the procedure is PSPACE-complete (add reference?), we would expect an exponential time in functions of the number of nestings in the worst case, which is what we seem to get. This is normal, as adding a nesting doubles the number of leaves. A table and a graph in the report mentioned earlier bring further evidence of this fact.


