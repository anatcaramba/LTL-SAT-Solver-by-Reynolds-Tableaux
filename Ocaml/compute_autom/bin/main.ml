open Printf

exception Get_rid_excep of string

type ltl =
| P 
| Q
| Top
| Bot
| Neg of ltl
| And of ltl * ltl
| Or of ltl * ltl
| F of ltl
| G of ltl
| X of ltl  (*basic type for ltl formulas*)

let rec string_ltl (phi:ltl) =
    match phi with
    |P-> "P"
    |Q-> "Q"
    |Top->"T"
    |Bot ->"B"
    |Neg psi ->  "Neg ("^((string_ltl psi)^")")
    |And (psi1,psi2)-> ("("^((string_ltl psi1) ^ ") ^ (")) ^(string_ltl psi2^")")
    |Or (psi1,psi2)->("("^((string_ltl psi1) ^ ") u (")) ^(string_ltl psi2^")")
    |F psi ->"F ("^ ((string_ltl psi)^")")
    |G psi ->"G ("^ ((string_ltl psi)^")")
    |X psi ->"X ("^ ((string_ltl psi)^")") (*turns a ltl formula into a printable string*)



let rec nnf (phi:ltl)=
    match phi with 
    |P->P |Neg P-> Neg P
    |Q->Q |Neg Q -> Neg Q
    |Top->Top|Neg Top -> Top
    |Bot->Bot|Neg Bot -> Bot
    |And (psi1, psi2) -> And ((nnf psi1), (nnf psi2)) |Neg (And (psi1, psi2)) -> Or ((nnf (Neg psi1)), nnf(Neg psi2))
    |Or (psi1, psi2) -> Or ((nnf psi1), (nnf psi2)) |Neg (Or(psi1, psi2)) -> And ((nnf (Neg psi1)), nnf(Neg psi2))
    |F psi -> F(nnf psi)|Neg(F psi) -> G(nnf (Neg psi))
    |G psi -> G(nnf psi)|Neg(G psi) -> F(nnf (Neg psi))
    |X psi -> X (nnf psi)| Neg(X psi) -> X(nnf(Neg psi))
    |Neg(Neg psi)-> nnf psi (*computes negative normal form, nnf*)


    
let phi = (And(Neg (F P),P))
let _ = printf "%s\n"(string_ltl phi)
let _ = printf "%s\n"(string_ltl (nnf phi))

let rec s_plus (phi:ltl)=
    match phi with
    |P->[P]|Q->[Q]|Top->[Top]|Bot->[Bot]
    |And(psi1,psi2)|Or(psi1,psi2)->phi::((s_plus psi1) @ (s_plus psi2))
    |Neg psi|X psi -> phi :: (s_plus psi)
    |F psi|G psi-> phi :: ((X phi) ::(s_plus psi)) (*computes S+, augmented version of subfomulas*)


let _ = List.iter (fun x -> (printf "%s\n"(string_ltl x))) (s_plus phi)

let rec contains_bot (l:ltl list)=
    match l with
    |[]->false
    |phi::l0->if phi=Bot then true else(if phi=Neg Top then true else contains_bot l0) (*checks if Bot or NegTop is in l*)

let rec contains_contra_0 (l:ltl list) (m:ltl list)=
    match l with
    |[]->false
    |psi::l0->match m with
        |[]->contains_contra_0 l0 l0
        |phi::m0 ->if psi=Neg phi then true else (if phi=Neg psi then true else contains_contra_0 l m0)
        (*intermediary version of contains_contra*)

let contains_contra (l:ltl list) =
    contains_contra_0 l l (*checks if the list contains contradictory formulas*)

let rec contains_top_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->if phi=Top then k else contains_top_0 l0 (k+1) 

let contains_top (l:ltl list)=
    contains_top_0 l 1 (*returns 0 if Top is not in l, and k+1 if Top is at index k*)

let rec get_rid_top (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "top")
        |phi::l0->if k=0 then raise (Get_rid_excep "top") else(
            if k=1 then match phi with
                |Top->l0@m
                |_->raise (Get_rid_excep "top")
                else(get_rid_top l0 (phi::m)(k-1)))
        (*gets rid of a top at index k; the order is changed*)
        (*if contains_top l=k,the parameter must be k. Inititally m=[]*)

let rec contains_neg_bot_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->if phi=Neg(Bot) then k else contains_neg_bot_0 l0 (k+1) 
let contains_neg_bot (l:ltl list)=
    contains_neg_bot_0 l 1 (*returns 0 if Top is not in l, and k+1 if Top is at index k*)


let rec get_rid_neg_bot (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "Neg Bot")
        |phi::l0->if k=0 then raise (Get_rid_excep "Neg Bot") else(
            if k=1 then match phi with
                |Neg(Bot)->l0@m
                |_->raise (Get_rid_excep "Neg Bot")
                else(get_rid_neg_bot l0 (phi::m)(k-1)))
        (*gets rid of a Neg(bot) at index k; the order is changed*)
        (*if contains_top l=k,the parameter must be k. Inititally m=[]*)

let rec contains_conj_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |And(psi1,psi2)->k
        |_->contains_conj_0 l0 (k+1)
        
let contains_conj (l:ltl list)=
    contains_conj_0 l 1  (*returns 0 if there is no conj in l, and k+1 if there is one at index k*)


let rec get_rid_conj (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "conj")
        |phi::l0->if k=0 then raise (Get_rid_excep "conj") else(
            if k=1 then match phi with
                |And(psi1,psi2)->l0@(psi1::(psi2::m))
                |_->raise(Get_rid_excep "conj")
                else(get_rid_conj l0 (phi::m)(k-1)))
        (*replaces a conj at index k by the two fml; the order is changed*)
        (*if contains_conj l=k,the parameter must be k. Inititally m=[]*)


let rec contains_neg_disj_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |Neg(Or(psi1,psi2))->k
        |_->contains_neg_disj_0 l0 (k+1) 
        
let contains_neg_disj (l:ltl list) = 
    contains_neg_disj_0 l 1 (*returns 0 if there is no neg of disj in l, and k+1 if there is one at index k*)

let rec get_rid_neg_disj (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "neg of disj")
        |phi::l0->if k=0 then raise (Get_rid_excep "double neg") else(
            if k=1 then match phi with
                |Neg(Or(psi1,psi2))->l0@(Neg(psi1)::(Neg(psi2)::m))
                |_->raise (Get_rid_excep "double neg")
                else(get_rid_neg_disj l0 (phi::m)(k-1)))
        (*replaces a neg of disj at index k by the two fml; the order is changed*)
        (*if contains_neg_disj l=k,the parameter must be k. Inititally m=[]*)


let rec contains_neg_neg_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |Neg(Neg(psi))->k
        |_->contains_neg_neg_0 l0 (k+1) 

let contains_neg_neg (l:ltl list) = 
    contains_neg_neg_0 l 1  (*returns 0 if there is no double neg in l, and k+1 if there is one at index k*)

let rec get_rid_neg_neg (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "double neg")
        |phi::l0->if k=0 then raise (Get_rid_excep "double neg") else(
            if k=1 then match phi with
                |Neg(Neg psi)->l0@(psi::m)
                |_->raise (Get_rid_excep "double neg")
                else(get_rid_neg_neg l0 (phi::m)(k-1)))
        (*replaces a double neg at index k by the equiv formula; the order is changed*)
        (*if contains_neg_neg l=k,the parameter must be k. Inititally m=[]*)


let rec contains_G_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |G(psi)->k
        |_->contains_G_0 l0 (k+1) 
let contains_G (l:ltl list)= 
    contains_G_0 l 1 (*returns 0 if there is no G formula in l, and k+1 if there is one at index k*)

let rec get_rid_G (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "G")
        |phi::l0->if k=0 then raise (Get_rid_excep "G") else(
            if k=1 then match phi with
                |G psi->l0@(X(G psi)::(psi::m))
                |_->raise (Get_rid_excep "G")
                else(get_rid_G l0 (phi::m)(k-1)))
        (*replaces a G formula at index k by the two required formula; the order is changed*)
        (*if contains_G l=k,the parameter must be k. Inititally m=[]*)        
            
let rec contains_neg_F_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |Neg(F(psi))->k
        |_->contains_neg_F_0 l0 (k+1) 
let contains_neg_F (l:ltl list)= 
    contains_neg_F_0 l 1 (*returns 0 if there is no neg F in l, and k+1 if there is one at index k*)

let rec get_rid_neg_F (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "neg F")
        |phi::l0->if k=0 then raise (Get_rid_excep "neg F") else(
            if k=1 then match phi with
                |Neg(F psi)->l0@(X(Neg(F psi))::(Neg(psi)::m))
                |_->raise (Get_rid_excep "neg F")
                else(get_rid_neg_F l0 (phi::m)(k-1)))
        (*replaces a neg F formula at index k by the two required formula; the order is changed*)
        (*if contains_neg_F l=k,the parameter must be k. Inititally m=[]*)   

let rec contains_disj_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |Or(psi1,psi2)->k
        |_->contains_disj_0 l0 (k+1) 
let contains_disj (l:ltl list)= 
    contains_disj_0 l 1 (*returns 0 if there is no disj in l, and k+1 if there is one at index k*)

let rec get_rid_disj (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "disj")
        |phi::l0->if k=0 then raise (Get_rid_excep "disj") else(
            if k=1 then match phi with
                |Or(psi1,psi2)->(function 0->l0@(psi1::m)|1->l0@(psi2::m)|_->raise (Get_rid_excep "disj"))
                |_->raise (Get_rid_excep "disj")
                else(get_rid_disj l0 (phi::m)(k-1)))
        (*removes a disjunction formula and replaces it with two versions of the new list, one with psi1, the other with psi2*)

let rec contains_F_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |F psi->k
        |_->contains_F_0 l0 (k+1) 
let contains_F (l:ltl list)= 
    contains_F_0 l 1 (*returns 0 if there is no F in l, and k+1 if there is one at index k*)

let rec get_rid_F (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "F")
        |phi::l0->if k=0 then raise (Get_rid_excep "F") else(
            if k=1 then match phi with
                |F psi->(function 0->l0@(psi::m)|1->l0@(X(F psi)::m)|_->raise (Get_rid_excep "F"))
                |_->raise (Get_rid_excep "F")
                else(get_rid_F l0 (phi::m)(k-1)))
        (*removes a F formula and replaces it with the two right versions of the new list *)

let rec contains_neg_conj_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |Neg(And(psi1,psi2))->k
        |_->contains_neg_conj_0 l0 (k+1) 
let contains_neg_conj (l:ltl list)= 
    contains_neg_conj_0 l 1 (*returns 0 if there is no neg of conj in l, and k+1 if there is one at index k*)

let rec get_rid_neg_conj (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "neg conj")
        |phi::l0->if k=0 then raise (Get_rid_excep "neg conj") else(
            if k=1 then match phi with
                |Neg(And(psi1,psi2))->(function 0->l0@(Neg psi1::m)|1->l0@(Neg psi2::m)|_-> raise (Get_rid_excep "neg conj"))
                |_->raise (Get_rid_excep "neg conj")
                else(get_rid_neg_conj l0 (phi::m)(k-1)))
        (*removes a neg of a conj formula and replaces it with the two right versions of the new list*)

let rec contains_neg_G_0 (l:ltl list) (k:int)=
    match l with
    |[]->0
    |phi::l0->match phi with
        |Neg(G psi)->k
        |_->contains_neg_G_0 l0 (k+1) 
let contains_neg_G (l:ltl list)= 
    contains_neg_G_0 l 1 (*returns 0 if there is no neg G in l, and k+1 if there is one at index k*)

let rec get_rid_neg_G (l:ltl list) (m:ltl list)(k:int)=
    match l with 
        |[]->raise (Get_rid_excep "neg G")
        |phi::l0->if k=0 then raise (Get_rid_excep "neg G") else(
            if k=1 then match phi with
                |Neg(G psi)->(function 0->l0@(Neg psi::m)|1->l0@(X(Neg(G psi))::m)|_->raise (Get_rid_excep "neg G"))
                |_->raise (Get_rid_excep "neg G")
                else(get_rid_neg_G l0 (phi::m)(k-1)))
        (*removes a neg G formula and replaces it with the two right versions of the new list *)



let rec apply_trans (l:ltl list)=
    match l with 
        |[]->[]
        |phi::l0-> match phi with
                |X psi->psi::apply_trans l0
                |Neg(X psi)->Neg(psi)::apply_trans l0
                |_->phi::apply_trans l0
        (*applies transition rule *)
        
let l = s_plus phi
let _ = List.iter (fun x -> (printf "%s\n"(string_ltl x))) (l)
let _ = printf "%b\n" (contains_bot l)
let _ = printf "%i\n"(contains_top l)
let _ = printf "%i\n"(contains_neg_F l)
let _ = List.iter (fun x -> (printf "%s\n"(string_ltl x))) (get_rid_neg_F l [] (contains_neg_F l))


let rec tableau (l:ltl list) =
    match l with
    |[]->true (*empty rule*)
    |phi::l0-> contains_bot l || contains_contra l || (if (contains_top l !=0) then tableau (get_rid_top l [] (contains_top l)) else
        if (contains_neg_bot l !=0) then tableau(get_rid_neg_bot [] l (contains_neg_bot l))else
        if (contains_conj l !=0) then tableau(get_rid_conj l [] (contains_conj l))else
        if (contains_neg_disj l !=0) then tableau (get_rid_neg_disj l [] (contains_neg_disj l))else
        if (contains_G l !=0) then tableau(get_rid_G l [] (contains_G l))else
        if (contains_neg_F l !=0) then tableau (get_rid_neg_F l [] (contains_neg_F l)) else
        if (contains_neg_neg l !=0) then tableau(get_rid_neg_neg l [] (contains_neg_neg l))else
        if (contains_disj l !=0) then let l0 = get_rid_disj l [](contains_disj l) in tableau (l0 0)||tableau (l0 1)else
        if (contains_neg_conj l !=0) then let l0 = get_rid_neg_conj l [](contains_neg_conj l) in tableau (l0 0)|| tableau (l0 1)else
        if (contains_F l !=0) then let l0 = get_rid_F l [](contains_F l) in tableau (l0 0)||tableau (l0 1)else
        if (contains_neg_G l !=0) then let l0 = get_rid_neg_G l [](contains_neg_G l) in tableau (l0 0)|| tableau (l0 1)else
        (*if loop then apply rule else
        if prune... else if prune0... else*)
        tableau (apply_trans l))
         







