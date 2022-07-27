open OUnit2
open Test_func 
  
let id x = x

let test_string_ltl (name:string) (exp_output:string) (input:ltl)=
("string_ltl "^name)>::(fun _ -> assert_equal exp_output (string_ltl input) ~printer:id)

let test_static_rule (name:string) (exp_output:ltl_op option) (input: ltl list)=
("static_rule "^name)>::(fun _->assert_equal exp_output (static_rule input) ~printer:(string_option string_ltl_op))


let test_main_op (name:string) (exp_output:ltl_op) (input: ltl)=
("main_op "^name)>::(fun _->assert_equal exp_output (main_op input) ~printer:string_ltl_op)

let test_get_rid_Unary (name:string)(exp_output:ltl list)(input_list:ltl list)(input_op:ltl_op)=
("get_rid_Unary "^name)>::(fun _->assert_equal exp_output (get_rid_Unary input_op input_list) ~printer:string_ltl_list)

let test_get_rid_Binary (name:string)(exp_output:ltl list)(input_list : ltl list)(input_op:ltl_op)(input_bool:bool)=
("get_rid_Binary "^name)>::(fun _->assert_equal exp_output (get_rid_Binary input_op input_list input_bool) ~printer:string_ltl_list)

let test_loop_applies (name:string)(exp_output:bool)(input:ltl list list)=
("loop_applies "^name)>::(fun _->assert_equal exp_output (loop_applies input) ~printer:string_of_bool)

let test_prune_applies (name:string)(exp_output:bool)(input:ltl list list)=
("prune_applies "^name)>::(fun _->assert_equal exp_output (prune_applies input) ~printer:string_of_bool)

let test_sat (name:string)(exp_output:bool)(input:ltl)=
("sat "^name)>::(fun _->assert_equal exp_output (sat input) ~printer:string_of_bool)

let tests = "Tests" >::: [
  (*tests for string_ltl*)
  test_string_ltl "Prop" "P" (Prop 'P');
  test_string_ltl "Neg F (And)" "Neg(F((P)^(Q)))" (Neg(F(And(Prop 'P',Prop 'Q'))));
  test_string_ltl "X Or G" "(X(T))u(G(B))" (Or(X Top,G Bot));

  (*tests for static_rule*)
  test_static_rule "P and XP" None [Prop 'P';X (Prop 'P')];
  test_static_rule "Empty" None [];
  test_static_rule "XF" (Some F_op) [Prop 'P';Prop 'Q';X (Prop 'P');F(X(And(Prop 'P',Prop 'Q')));Neg (Prop 'Q')];

  (*tests for main_op*)
  test_main_op "Neg P" Prop_op (Neg (Prop 'P'));
  test_main_op "And" And_op (And(Neg (Prop 'Q'),X(Neg (Prop 'P'))));
  test_main_op "Double Neg" NNeg_op (Neg(Neg(Neg (Prop 'Q'))));

  (*tests for get_rid_Unary*)
  test_get_rid_Unary "Neg F" [Prop 'P';Neg(And(Prop 'P',Prop 'Q'));X(Neg(F(And(Prop 'P',Prop 'Q'))));Or(X Top,G Bot)] [Prop 'P';Neg(F(And(Prop 'P',Prop 'Q')));Or(X Top,G Bot)] NF_op ;
  test_get_rid_Unary "And" [Prop 'P';Prop 'P';Prop 'Q';Or(X Top,G Bot)] [Prop 'P';And(Prop 'P',Prop 'Q');Or(X Top,G Bot)] And_op;

  (*tests for get_rid_Binary*)
  test_get_rid_Binary "Neg G case 1" [Prop 'P';Neg(And(Prop 'P',Prop 'Q'));Or(X Top,G Bot)] [Prop 'P';Neg(G(And(Prop 'P',Prop 'Q')));Or(X Top,G Bot)] NG_op false ;
  test_get_rid_Binary "Neg G case 2" [Prop 'P';X(Neg(G(And(Prop 'P',Prop 'Q'))));Or(X Top,G Bot)] [Prop 'P';Neg(G(And(Prop 'P',Prop 'Q')));Or(X Top,G Bot)] NG_op true ;
  test_get_rid_Binary "Or case 1" [Prop 'P';Neg(G(And(Prop 'P',Prop 'Q')));X Top] [Prop 'P';Neg(G(And(Prop 'P',Prop 'Q')));Or(X Top,G Bot)] Or_op false ;
  test_get_rid_Binary "Or case 2" [Prop 'P';Neg(G(And(Prop 'P',Prop 'Q')));G Bot] [Prop 'P';Neg(G(And(Prop 'P',Prop 'Q')));Or(X Top,G Bot)] Or_op true;

  (*tests for loop_applies*)
  test_loop_applies "does not apply" false  ([[G(Prop 'P')];[Prop 'P';X(G(Prop('P')))]]);
  test_loop_applies "does apply" true ([[Prop 'P';X(G(Prop('P')))];[G(Prop 'P')];[Prop 'P';X(G(Prop('P')))]]  ); 

  (*tests for prune_applies*)
  test_prune_applies "applies" true ([[Prop 'P';Prop 'Q';X(G(And(Prop 'P',Prop 'Q')));X(F(Neg(Prop 'P')))];[G(And(Prop 'P',Prop 'Q'));F(Neg(Prop 'P'))];[Prop 'P';Prop 'Q';X(G(And(Prop 'P',Prop 'Q')));X(F(Neg(Prop 'P')))];[G(And(Prop 'P',Prop 'Q'));F(Neg(Prop 'P'))];[Prop 'P';Prop 'Q';X(G(And(Prop 'P',Prop 'Q')));X(F(Neg(Prop 'P')))]]);
  test_prune_applies "does not apply" false ([[Prop 'P';Prop 'Q';X(G(And(Prop 'P',Prop 'Q')));X(F(Neg(Prop 'P')))];[G(And(Prop 'P',Prop 'Q'))];[Prop 'P';Prop 'Q';X(G(And(Prop 'P',Prop 'Q')));X(F(Neg(Prop 'P')))];[G(And(Prop 'P',Prop 'Q'));Neg(Prop 'P')];[Prop 'P';Prop 'Q';X(G(And(Prop 'P',Prop 'Q')));X(F(Neg(Prop 'P')))]]);

  (*tests for sat*)
  test_sat "classical disj" true (And(Prop 'P',Or(Prop 'Q',Neg(Prop 'R')))); 
  test_sat "G of prop" true (G (Prop 'P'));
  test_sat "G p and F (not p)" false (And(G(And(Prop 'P',Prop 'Q')),F(Neg(Prop 'P'))));
  ]

let _ = run_test_tt_main tests