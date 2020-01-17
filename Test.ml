(*------------------------TESTS-------------------------*)
print_endline("----------------------TESTS--------------------");;

let env0 = emptyenv Unbound;;

(*creo un dizionario con una coppia chiave-valore, in cui i valori sono interi*)
print_endline("creo un dizionario con una coppia chiave-valore, in cui i valori sono interi")
let d = Dict(Pair("mele", Eint(2), Empty));;
(*controllo che lo abbia creato nel modo giusto valutando d*)
let dstart = eval d env0;;
dstart;;

print_endline("provo a creare un dizionario con due coppie chiave-valore, in cui i valori sono interi e booleani");;
eval (Dict(Pair("intero", Eint(1), Pair("booleano", Ebool(true), Empty)))) env0;;




(*---Test Insert---*)
print_endline("----------------------TEST Insert--------------------");;

(*inserisco le banane*)
print_endline("Inserisco le banane");;
let d1 = Insert("banane", Eint(4), d);;
eval d1 env0;;

(*inserisco pere e kiwi*)
print_endline("Inserisco pere e kiwi");;
let d2 = Insert("pere", Eint(6), Insert("kiwi", Eint(5), d1));;
let magazzinoFull = eval d2 env0;;
magazzinoFull;;

(*provo ad inserire una chiave già presente*)
print_endline("Provo ad inserire una chiave già presente");;
eval (Insert("pere", Eint(6), d2)) env0;;


(*---Test Delete---*)
print_endline("----------------------TEST Delete--------------------");;

magazzinoFull;;

print_endline("Elimino le banane");;
(*let d3 = Delete(d2, "banane");;*)
eval (Delete(d2, "banane")) env0;;

(*provo ad eliminare una chiave non presente nel dizionario*)
print_endline("Provo ad eliminare una chiave non presente nel dizionario: il dizionario non viene modificato");;
eval (Delete(d2, "fragole")) env0;;


(*---Test Has_Key---*)

print_endline("----------------------TEST Has_Key--------------------");;
magazzinoFull;;
print_endline("Has_Key mele?");;
eval (Has_Key("mele", d2)) env0;;
print_endline("Has_Key fragole?");;
eval (Has_Key("fragole", d2)) env0;;

(*---Test Filter---*)
print_endline("----------------------TEST Filter--------------------");;
magazzinoFull;;
print_endline("Filtro pere e banane");;
eval (Filter(["banane"; "pere"], d2)) env0;;

print_endline("----------------------TEST Iterate--------------------");;

let magazzinoFull = eval (Dict(Pair("mele", Eint(2), Pair("banane", Eint(4), Pair("pere", Eint(6), Pair("kiwi", Eint(5), Empty)))))) env0;;
print_endline("Applico la funzione fun x -> x + 1 a tutti gli elementi del dizionario magazzinoFull");;
eval (Iterate((Fun("x", Sum(Den "x", Eint(1)))), Dict(Pair("mele", Eint(2), Pair("banane", Eint(4), Pair("pere", Eint(6), Pair("kiwi", Eint(5), Empty))))))) env0;;

print_endline("----------------------TEST Fold--------------------");;

let magazzinoFull = eval (Dict(Pair("mele", Eint(2), Pair("banane", Eint(4), Pair("pere", Eint(6), Pair("kiwi", Eint(5), Empty)))))) env0;;

print_endline("Applico la funzione fun acc x -> acc + x + 1 sequenzialmente al dizionario magazzinoFull");;

let result = eval (Fold(BinFun("acc", "x", Sum(Den "acc", Sum(Den "x", Eint 1))), Dict(Pair("mele", Eint(2), Pair("banane", Eint(4), Pair("pere", Eint(6), Pair("kiwi", Eint(5), Empty))))))) (emptyenv Unbound);; 