
type ide = string;;

type exp = 
		| Eint of int 
		| Ebool of bool
		| Estring of string
		| Den of ide 
		| Prod of exp * exp 
		| Sum of exp * exp 
		| Diff of exp * exp 
		| Eq of exp * exp 
		| Minus of exp 
		| IsZero of exp 
		| Or of exp * exp 
		| And of exp * exp 
		| Not of exp 
		| Ifthenelse of exp * exp * exp 
		| Let of ide * exp * exp 
		| Fun of ide * exp 
		| BinFun of ide * ide * exp (*funzione binaria*)
		| FunCall of exp * exp
		| BinFunCall of exp * exp * exp (* chiamata funzione binaria *)
		| Letrec of ide * exp * exp

        (* dictionary *)
        | Dict of pairlist
        | Insert of ide * exp * exp (* key - value - dictionary *)
        | Delete of exp * ide       (* dictionary - key *)
        | Has_Key of ide * exp      (* key - dictionary *)
        | Iterate of exp * exp      (* function - dictionary *)
        | Fold of exp * exp         (* function - dictionary *)
        | Filter of ide list * exp  (* key list - dictionary *)        
        
        and pairlist = Empty | Pair of ide * exp * pairlist;;   (* lista di coppie chiave-valore *)


(*ambiente polimorfo*)
type 't env = ide -> 't;;

let emptyenv (v : 't) = function x -> v;;

let applyenv (r : 't env) (i : ide) = r i;;

let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = 
		| Int of int 
		| Bool of bool
		| String of string 
		| Unbound
		| FunVal of evFun 
		| BinFunVal of ide * ide * exp * evT env		(*funzione binaria *)
		| RecFunVal of ide * evFun

        | Dictval of (ide * evT) list

and evFun = ide * exp * evT env;;



(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	| "int" -> (match v with
						| Int(_) -> true 
						| _ -> false) 
	| "bool" -> (match v with
						| Bool(_) -> true 
						| _ -> false)
	| "string" -> (match v with
						| String(_) -> true
						| _ -> false)
	| "dictionary" -> (match v with
						| Dictval(d) -> (let rec isDictionary x = 
											(match x with
												| [] -> true
												| (k, value) :: [] -> true
												| (k, value) :: (k1, value1) :: xs -> (match (value, value1) with
																						| (Int(_), Int(_)) -> isDictionary ((k1, value1) :: xs)
																						| (Bool(_), Bool(_)) -> isDictionary ((k1, value1) :: xs)
																						| (_, _) -> false
																					) 
											)
										in isDictionary d)
						| _ -> false 
					)
	| _ -> failwith("not a valid type");;



(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
			| (Int(n),Int(u)) -> Int(n*u)
            | (_ , _) -> failwith("Type error"))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		    | (Int(n),Int(u)) -> Int(n+u)
            | (_ , _) -> failwith("Type error"))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		    | (Int(n),Int(u)) -> Int(n-u)
            | (_ , _) -> failwith("Type error"))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		    | (Int(n),Int(u)) -> Bool(n=u)
            | (_ , _) -> failwith("Type error"))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	    | Int(n) -> Int(-n)
            | _ -> failwith("Type error"))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		    | Int(n) -> Bool(n=0)
            | _ -> failwith("Type error"))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		    | (Bool(b),Bool(e)) -> (Bool(b||e))
            | (_ , _) -> failwith("Type error"))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		    | (Bool(b),Bool(e)) -> Bool(b&&e)
            | (_ , _) -> failwith("Type error"))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		    | Bool(true) -> Bool(false) 
            | Bool(false) -> Bool(true)
            | _ -> failwith("Type error"))
	else failwith("Type error");;



(*FUNZIONI DI SUPPORTO PER OPERAZIONI PRIMITIVE DI GESTIONE DIZIONARIO*)

(* se l'elemento v è presente nella lista list restituisce true, altrimenti restituisce false *)
let rec listMember v list = match list with
						| [] -> false
						| x :: xs -> if(x = v) then true else listMember v xs;;

(* se la chiave k è presente nel dizionario d restituisce il valore booleano true, altrimenti restituisce false *)
let rec dictMember k d = (match d with
					| [] -> false 
					| (key, value) :: ds -> if(key = k) then true
											else dictMember k ds);;

(* eccezioni *)
exception Type_error of string;;



(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	| Eint n -> Int n 
	| Ebool b -> Bool b
	| Estring s -> String s
	| IsZero a -> iszero (eval a r) 
	| Den i -> applyenv r i 
	| Eq(a, b) -> eq (eval a r) (eval b r) 
	| Prod(a, b) -> prod (eval a r) (eval b r) 
	| Sum(a, b) -> sum (eval a r) (eval b r) 
	| Diff(a, b) -> diff (eval a r) (eval b r) 
	| Minus a -> minus (eval a r) 
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	| Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
	| Fun(i, a) -> FunVal(i, a, r)
	| BinFun(acc, i, a) -> BinFunVal(acc, i, a, r)			(* definizione di funzione binaria, in cui il primo argomento sarà l'accumulatore *)
	| FunCall(f, eArg) -> (* scoping statico *)
		let fClosure = (eval f r) in
			(match fClosure with
				| FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) 
				| RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv 
				| _ -> failwith("non functional value"))
	| BinFunCall(f, arg1, arg2) -> 							(* chiamata di una funzione binaria non ricorsiva, il cui primo argomento è un accumulatore *)
		let fClosure = (eval f r) in
				(match fClosure with
				  | BinFunVal(a1, a2, body, fDecEnv) -> let env1 = bind fDecEnv a1 (eval arg1 r) in
				  										let env2 = bind env1 a2 (eval arg2 r) in
														  eval body env2
				  | _ -> failwith("not a binary function")
				) 
	| Letrec(f, funDef, lbody) ->
        		(match funDef with
            		| Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval lbody r1 
					| _ -> failwith("non functional def"))
    
    (*IMPLEMENTAZIONE INTERPRETE PER NUOVO TIPO PRIMITIVO E NUOVE OPERAZIONI PRIMITIVE*)

	(* un dizionario è una lista di coppie chiave-valore di tipo (ide*evT) list *)
	| Dict(d) -> (let dict = (evalPairlist d r) in
					if(typecheck "dictionary" (Dictval(dict))) then Dictval(dict)
					(*else failwith("not a dictionary: different value types"))*)
					(*else raise (Type_error "not a dictionary: different value types")*)
					else String(Printexc.to_string(Type_error "not a dictionary: different value types"))
					)

	(* se non è già presente, inserisce in testa la coppia (key, value) nel dizionario d *)
	| Insert(key, value, d) -> (match eval d r with
								| Dictval(dict) -> if(dictMember key dict) then (*failwith("Key already in the dictionary")*)
																			String(Printexc.to_string(Type_error "key already in the dictionary"))

													else (match dict with
															| [] -> Dictval((key, (eval value r)) :: dict)
															| (k, v) :: ds -> (match (v, (eval value r)) with
																				| (Int(x), Int(y)) -> Dictval((key, (eval value r)) :: dict)
																				| (Bool(x), Bool(y)) -> Dictval((key, (eval value r)) :: dict)
																				| (_, _) -> (*failwith("type error: wrong value type")*)
																							String(Printexc.to_string(Type_error "wrong value type"))
)
													)
													
								| _ -> failwith("Type error: 3rd argument is not a dictionary"))

	(* se presente, elimina dal dizionario d, la coppia che ha chiave key *)
	| Delete(d, key) -> (match eval d r with
							| Dictval(dict) -> Dictval(deleteFromDict dict key)
							| _ -> failwith("Type error: 1st argument is not a dictionary"))

	(* restituisce Bool(true) se esiste nel dizionario una coppia del (key, _), altrimenti, restituisce Bool(false) *)
	| Has_Key(key, d) -> (match eval d r with			
							| Dictval(dict) -> Bool(dictMember key dict)
							| _ -> failwith("Type error: 2nd argument of function Has_Key is not of type Dict"))

	(* restituisce un dizionario di tipo Dictval ai cui valori è stata applicata la funzione f *)
	| Iterate(f, d) -> (match d with
						| Dict dict -> if(typecheck "dictionary" (Dictval(evalPairlist dict r))) then Dictval(iter f dict r)
										else failwith("Type error: not a dictionary")
						| _ -> failwith("Type error: function not applied to a dictionary"))
	
	(* restituisce un valore risultato dell'applicazione della funzione binaria f (con accumulatore) ai valori del dizionario *)
	| Fold(f, d) -> 
					(match eval d r with
						| Dictval dict -> (match f with
											| BinFun(acc, i, a) -> 
																	(match a with
																		| Sum(_, _) -> (accFun (Int(0)) f dict r)
																		| Diff(_, _) -> (accFun (Int(0)) f dict r)
																		| Prod(_, _) -> (accFun (Int(1)) f dict r) 
																		| Or (_, _) -> (accFun (Bool(false)) f dict r)
																		| And (_, _) -> (accFun (Bool(true)) f dict r)
																		| Eq(_, _) -> (accFun (Bool(true)) f dict r)
																		| _ -> failwith("operation not supported")
																	)
											| _ -> failwith("type error: not a binary function")
										)						
						| _ -> failwith("type error, not a dictionary")
					)

	(* restituisce un dizionario in cui le chiavi appertengono tutte alla lista di chiavi kl *)
	| Filter(kl, d) -> (match eval d r with
						| Dictval(dict) -> Dictval(filter kl dict)
						| _ -> failwith("Type error: 2nd argument is not a dictionary"))

		(* valuta il tipo pairlist restituendo una lista di coppie (ide * evT) *)
	and evalPairlist (pl : pairlist) (r : evT env) : (ide * evT) list =
        (match pl with
        | Empty -> []
        | Pair(key, value, rl) -> (key, (eval value r)) :: evalPairlist rl r)

		(* effettua l'operazione Delete in un dizionario *)
	and deleteFromDict (dict : (ide * evT) list) (key : ide) =
			(match dict with 
			| [] -> []
			| (k,v) :: ds -> if(key = k) then deleteFromDict ds key
								else (k,v) :: (deleteFromDict ds key))
	
		(* restituisce una lista di coppie chiave-valore le cui chiavi appartendono alla lista l passata come argomento *)
	and filter (l : ide list) (dict : (ide * evT) list) : ((ide * evT) list) =
			(match dict with
				| [] -> []
				| (key, value) :: ds -> if(listMember key l) then (key, value) :: (filter l ds)
										else (filter l ds))
	
		(* applica la funzione ff, passata come argomento, a tutti i valori del dizionario dict *)
	and iter (ff : exp) (dict : pairlist) (amb : evT env) : (ide * evT) list =
			(match dict with
				| Empty -> []
				| Pair(k, v, pl) -> (k, eval (FunCall(ff, v)) amb ) :: iter ff pl amb
			)

		(* applica sequenzialmente una funzione a tutti i valori del dizionario, accumulando piano piano il risultato delle varie computazioni in un accumulatore acc *)
	and accFun (acc : evT) (f : exp) (dict : (ide*evT) list) (amb : evT env) : evT =
			(match dict with
				| [] -> acc 
				| (k, v) :: ds -> (match (acc, v) with
									| (Int(x), Int(y)) -> accFun (eval (BinFunCall(f, Eint(x), Eint(y))) amb) f ds amb
									| (Bool(x), Bool(y)) -> accFun (eval (BinFunCall(f, Ebool(x), Ebool(y))) amb) f ds amb
									| (Int(x), Bool(y)) -> accFun (eval (BinFunCall(f, Eint(x), Ebool(y))) amb) f ds amb
									| (Bool(x), Int(y)) -> accFun (eval (BinFunCall(f, Ebool(x), Eint(y))) amb) f ds amb
									| (_, _) -> failwith("type error: argument type not supported")
									)
			)

    ;;