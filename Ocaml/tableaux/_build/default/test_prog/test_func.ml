exception Get_rid_excep of string


(**Type corresponding to LTL formulas (the restricted fragment)*)
type ltl =
| Prop of char
| Top
| Bot
| Neg of ltl
| And of ltl * ltl
| Or of ltl * ltl
| F of ltl
| G of ltl
| X of ltl

(**Type characterizing LTL formulas by their main operator, following structure of static rules*)
type ltl_op =
| Prop_op
| Top_op
| NTop_op
| Bot_op
| NBot_op
| Neg_op
| NNeg_op
| And_op
| NAnd_op
| Or_op
| NOr_op
| F_op
| NF_op
| G_op
| NG_op
| X_op
| NX_op

(**Every node of the tree will contain the list of its ancestors*)
type tableau =
  Node of ltl list list

 
(**Computes main operator of any ltl formula, following structure of static rules*)
let main_op :ltl->ltl_op=function
|Prop c|Neg (Prop c)->Prop_op
|Top->Top_op
|Neg(Top)->NTop_op
|Bot->Bot_op
|Neg(Bot)->NBot_op
|F _->F_op
|Neg(F _)->NF_op
|G _->G_op
|Neg(G _)->NG_op
|And(_,_)->And_op
|Neg(And(_,_))->NAnd_op
|Or(_,_)->Or_op
|Neg(Or(_,_))->NOr_op
|Neg(Neg _ )-> NNeg_op
|X _->X_op
|Neg(X _)->NX_op

(*It would be nice to make this more complete, to get rid of a few useless parentheses*)
(**Turns phi into a printable string*)
let rec string_ltl (phi:ltl) =
match phi with
|Prop c ->String.make 1 c
|Top->"T"
|Bot ->"B"
|Neg psi -> "Neg("^((string_ltl psi)^")")
|And (psi1,psi2)-> ("("^((string_ltl psi1) ^ ")^(")) ^(string_ltl psi2^")")
|Or (psi1,psi2)->("("^((string_ltl psi1) ^ ")u(")) ^(string_ltl psi2^")")
|F psi ->"F("^ ((string_ltl psi)^")")
|G psi ->"G("^ ((string_ltl psi)^")")
|X psi ->"X("^ ((string_ltl psi)^")")

let rec string_ltl_list = function
  |[]->""
  |phi::[]->(string_ltl phi)
  |phi::l'->(string_ltl phi)^" ; "^(string_ltl_list l')


(**Turns a ltl_op into a printable string*)
let string_ltl_op : ltl_op->string = function
| Prop_op -> "Prop_op"
| Top_op -> "Top_op"
| NTop_op ->"NTop_op"
| Bot_op -> "Bot_op"
| NBot_op -> "NBot_op"
| Neg_op -> "Neg_op"
| NNeg_op -> "NNeg_op"
| And_op -> "And_op"
| NAnd_op -> "NAnd_op"
| Or_op -> "Or_op"
| NOr_op -> "NOr_op"
| F_op -> "F_op"
| NF_op -> "NF_op"
| G_op -> "G_op"
| NG_op -> "NG_op"
| X_op -> "X_op"
| NX_op -> "NX_op"

(**Computes negative normal form of phi*)
let rec nnf (phi:ltl)=
  match phi with
    |Prop _|Neg (Prop _)|Top|Neg Top|Bot|Neg Bot -> phi
    |And (psi1, psi2) -> And ((nnf psi1), (nnf psi2)) 
    |Neg (And (psi1, psi2)) -> Or ((nnf (Neg psi1)), nnf(Neg psi2))
    |Or (psi1, psi2) -> Or ((nnf psi1), (nnf psi2)) 
    |Neg (Or(psi1, psi2)) -> And ((nnf (Neg psi1)), nnf(Neg psi2))
    |F psi -> F(nnf psi)
    |Neg(F psi) -> G(nnf (Neg psi))
    |G psi -> G(nnf psi)
    |Neg(G psi) -> F(nnf (Neg psi))
    |X psi -> X(nnf psi)
    |Neg(X psi) -> X(nnf(Neg psi))
    |Neg(Neg psi)-> nnf psi


(**Computes the list of subformulas of phi, along with successors of F and G subformulas*)
let rec s_plus (phi:ltl)=
match phi with
|Prop _->[phi]
|Top->[Top]
|Bot->[Bot]
|And(psi1,psi2)|Or(psi1,psi2)->phi::((s_plus psi1) @ (s_plus psi2))
|Neg psi|X psi -> phi :: (s_plus psi)
|F psi|G psi-> phi :: ((X phi) ::(s_plus psi))


(**Returns true iff the list contains contradictory formulas*)
let contains_contra (l:ltl list) : bool =
  let contains_neg (l:ltl list)(phi:ltl):bool=
    List.exists(fun psi -> (psi = Neg phi)) l
  in
  List.exists(fun phi->contains_neg l phi) l



(**Applies transition rule*)
let rec apply_trans (l:ltl list)=
match l with
|[]->[]
|phi::l0-> match phi with
|X psi->psi::apply_trans l0
|Neg(X psi)->Neg(psi)::apply_trans l0
|_->phi::apply_trans l0


(**Returns true iff no rule applies to a formula*)
let is_exhausted :ltl->bool = function
|Prop _|Neg(Prop _)|X(_)|Neg(X(_))->true
|_->false


(**Returns true iff no static rule applies to l*)
let rec is_poised (l:ltl list):bool=
if contains_contra l then false else
  match l with
  |[]->false
  |phi::l'->if is_exhausted phi then (if l'=[] then true else is_poised l') else false


(**Returns Some k if the list contains a formula with main operator op at index k; None if it does nowhere *)
let contains_op = 
  let rec contains_op_0 (k:int)(op:ltl_op)(l:ltl list):int option=
  match l with
  |[]->None
  |phi::l0->if main_op phi=op then Some k else contains_op_0 (k+1) op l0 in
contains_op_0 0 


(*let init_hash_table (l:ltl):int->ltl=
  let sub_phi = s_plus l in 
  let indices = List.map *)

(**Takes list where the (0 or 1)-ary rule related to op can be applied, and does so.*)
let get_rid_Unary (op:ltl_op)(l:ltl list):ltl list=
  let rec get_rid_Unary_0 (k:int)(l:ltl list)(m:ltl list):ltl list = 
    match l with
    |[]->failwith "operator not found after exploring all the list"
    |phi::l'->if k=0 then 
      match phi with
      |Top|Neg Bot->m@l'
      |And(psi1,psi2)->m@(psi1::psi2::l')
      |Neg(Or(psi1,psi2))->m@((Neg psi1)::(Neg psi2) :: l')
      |Neg (Neg psi)->m@(psi::l')
      |G psi ->m@(psi :: X (G psi):: l')
      |Neg (F psi)-> m@(Neg psi :: (X (Neg (F psi))) :: l')
      |_->failwith "no 0-ary or unary rule applies"
    else get_rid_Unary_0 (k-1) l' (m@[phi]) in
  match contains_op op l with
      |None -> failwith "list does not contain operator"
      |Some k -> get_rid_Unary_0 k l []


(**Takes list where the (0 or 1)-ary rule related to op can be applied, and does so.*)
let get_rid_Binary (op:ltl_op)(l:ltl list):bool->ltl list=
  let rec get_rid_Binary_0 (k:int)(l:ltl list)(m:ltl list):bool->ltl list = match l with
    |[]->failwith "operator not found after exploring all the list"
    |phi::l'->if k=0 then match phi with
      |Or(psi1,psi2)->(function |false->m@(psi1::l')|true->m@(psi2::l'))
      |Neg(And(psi1,psi2))->(function |false->m@((Neg psi1)::l')|true->m@((Neg psi2)::l'))
      |F psi->(function |false->m@(psi::l') |true->m@((X(F psi))::l'))
      |Neg(G psi)->(function |false->m@((Neg psi)::l') |true->m@(X(Neg(G psi)))::l') 
      |_->failwith "no binary rule applies"
    else get_rid_Binary_0 (k-1) l' (m@[phi]) in
  match contains_op op l with
      |None -> failwith "list does not contain operator"
      |Some k -> get_rid_Binary_0 k l []
  

(**Returns true iff list l is included in list m sets-wise*)
let rec is_included (l:'a list) (m:'a list):bool=
    match l with
    |[]->true
    |phi::l'->List.exists (fun x->x=phi) m && is_included l' m

(**Returns true iff both lists are equal sets-wise*)    
let are_equal (l:'a list)(m:'a list):bool = 
  is_included l m && is_included m l




(**  Returns the list of indexes of the proper ancestors of t containing its list sets wise*)
let poised_ancestors_contain :tableau->int list = 
  let rec poised_ancestors_contain_0 (ll:ltl list list)(l:ltl list)(k:int):int list=
    match ll with
    |[]->[]
    |m::ll'->(if is_poised m && is_included l m then [k] else [])@(poised_ancestors_contain_0 ll' l (k+1)) in 
  function
  |Node([])->failwith "empty list of ancestors"
  |Node(l::ll)-> poised_ancestors_contain_0 ll l 1


(**Returns true iff all X-eventualities in gamma_u are satisfied in gamma_w*)
let rec all_X_ev_satisfied (gamma_w:ltl list)(gamma_u:ltl list):bool = 
  List.for_all(function
    |X (F psi)->List.exists(fun chi->chi= F psi)gamma_w
    |X (G psi)->List.exists(fun chi->chi= G psi)gamma_w
    |Neg(X (F psi))->List.exists(fun chi->chi=Neg (F psi))gamma_w
    |Neg(X (G psi))->List.exists(fun chi->chi= Neg (G psi))gamma_w
    |_->true)gamma_u
   


(**Returns true iff there exists an ancestor of age 0 to k-1 which satisfies all X-eventualities in the k-th ancestor*)
let rec exists_all_X_ev_sat (ll:ltl list list)(gamma_u:ltl list)(k:int):bool =
  if k=0 then false else 
  match ll with
  |[]->failwith ""
  |gamma_w::ll'->all_X_ev_satisfied gamma_w gamma_u || exists_all_X_ev_sat ll' gamma_u (k-1)

let loop_applies (t:tableau):bool=
  let i = poised_ancestors_contain t in
    List.exists(fun k->match t with
      |Node(ll)-> let gamma_u = List.nth ll k in
        exists_all_X_ev_sat ll gamma_u k) i













