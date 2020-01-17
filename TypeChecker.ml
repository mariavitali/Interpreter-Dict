type ide = string;;

type tval = 
        | TInt
        | TBool
        | TString
        | FunT of tval * tval   (* tipo dell'argomento * tipo del risultato *)
        | BinFunT of tval * tval * tval (* tipo arg1 * tipo arg2 * tipo del risultato *)

        (*nuovo tipo dizionario che è semplicemente una lista di coppie stringa-valore*)
        | TDict of (tval * tval) list;;

(*eccezioni*)
exception EmptyEnv;;


(*ambiente dei tipi*)

type tenv = ide -> tval;;

let bindT (r : tenv) (i : ide) (v : tval) =
    function x -> if x = i then v else r x;;

let tenv0 = fun (x: ide) -> raise EmptyEnv;;

(*bisogna definire un nuovo tipo texp apposito? Il problema principale è la dichiarazione di funzione, che nell' ambiente dei tipi ha un parametro in più, che specifica il tipo dell'argomento passato alla funzione*)
(*in questo contesto, le chiavi del dizionario hanno tipo Tstring, quindi non sono visti come ide, ma come exp/tval*)
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
		(*| Fun of ide * exp*)
    (*TIPO DELLA FUNZIONE LEGGERMENTE DIVERSO, PER ESSERE ADATTATO A UN CONTROLLO DEI TIPI*)
    | TFun of ide * tval * exp
    | TBinFun of ide * ide * tval * tval * exp
		| FunCall of exp * exp
    | BinFunCall of exp * exp * exp
		| Letrec of ide * exp * exp

        (* dictionary *)
    | Dict of pairlist 
    | Insert of exp * exp * exp (* key (string) - value (evT) - dictionary ((evT * evT) list) *)
    | Delete of exp * exp       (* dictionary - key *)
    | Has_Key of exp * exp      (* key - dictionary *)
    | Iterate of exp * exp      (* function - dictionary *)
    | Fold of exp * exp         (* function - dictionary *)
    | Filter of (exp list) * exp  (* key list - dictionary *)        
        
    and pairlist = Empty | Pair of exp * exp * pairlist;;

let rec teval e tenv : tval =
        match e with
            | Eint i -> TInt
            | Ebool b -> TBool
            | Estring s -> TString
            | Den s -> tenv s
            | Prod(e1, e2) -> (let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in
                                    (match (t1, t2) with
                                     | (TInt, TInt) -> TInt
                                     | (_, _) -> failwith("wrong type")))
            | Sum(e1, e2) -> (let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in
                                    (match (t1, t2) with
                                     | (TInt, TInt) -> TInt
                                     | (_, _) -> failwith("wrong type")))
            | Diff(e1, e2) -> (let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in
                                    (match (t1, t2) with
                                     | (TInt, TInt) -> TInt
                                     | (_, _) -> failwith("wrong type")))
            | Eq(e1, e2) -> (if((teval e1 tenv) = (teval e2 tenv)) then TBool
                            else failwith("wrong type"))
            | Minus x -> (match teval x tenv with
                            | TInt -> TBool
                            | _ -> failwith("wrong type"))
            | IsZero x -> (match teval x tenv with
                            | TInt -> TBool
                            | _ -> failwith("wrong type"))
            | Or(e1, e2) -> (let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in
                                    (match (t1, t2) with
                                     | (TBool, TBool) -> TBool
                                     | (_, _) -> failwith("wrong type")))
            | And(e1, e2) -> (let t1 = teval e1 tenv in 
                                let t2 = teval e2 tenv in
                                    (match (t1, t2) with
                                     | (TBool, TBool) -> TBool
                                     | (_, _) -> failwith("wrong type")))
            | Not x -> (match teval x tenv with
                            | TBool -> TBool
                            | _ -> failwith("wrong type"))
            | Ifthenelse (e, e1, e2) -> (let t = teval e tenv in
                                            (match t with
                                             | TBool -> let t1 = teval e1 tenv in
                                                            let t2 = teval e2 tenv in
                                                                (match(t1, t2) with
                                                                  | (TInt, TInt) -> TInt
                                                                  | (TBool, TBool) -> TBool
                                                                  | (_,_) -> failwith("wrong type"))
                                             | _ -> failwith ("wrong type")))
            | Let(i, e1, e2) -> (let t = teval e1 tenv in
                                        teval e2 (bindT tenv i t))
            | TFun(i, t1, e1) -> (let tenv1 = bindT tenv i t1 in
                                    let t2 = teval e1 tenv1 in FunT(t1, t2))
            | TBinFun(acc, i, tacc, ti, e1) -> (let tenv1 = bindT tenv acc tacc in
                                                let tenv2 = bindT tenv1 i ti in
                                                  let tres = teval e1 tenv2 in BinFunT(tacc, ti, tres))
            | FunCall(e1, e2) -> (let f = teval e1 tenv in
                                    (match f with
                                      | FunT(t1, t2) -> if((teval e2 tenv) = t1) then t2
                                                        else failwith("wrong type")
                                      | _ -> failwith ("wrong type")))
            | BinFunCall(funz, arg1, arg2) -> (let f = teval funz tenv in
                                              (match f with
                                                | BinFunT(tacc, ti, tres) -> if(((teval arg1 tenv) = tacc) && ((teval arg2 tenv)=ti) && (tacc=tres)) then tres
                                                                              else failwith("wrong type")
                                                | _ -> failwith("wrong type")))

            (* implementato solo per funzioni ricorsive che lavorano su interi *)                         
            | Letrec(f, funDef, body) -> (match funDef with
                                            | TFun(i, targ, fbody) -> (let newEnv = bindT tenv f (FunT(targ, TInt)) in 
                                                                        let t = teval funDef newEnv in
                                                                        teval body (bindT newEnv f t))
                                            | _ -> failwith("wrong type"))

            | Dict d -> (let dict = (tevalPairlist d tenv) in
                          let rec typecheckDict = fun dl -> 
                              (match dl with
                                | [] -> TDict([])
                                | (tk, tv) :: ds -> (match tk with
                                                      | TString -> (match ds with
                                                                      | [] -> TDict(dl)
                                                                      | (tk1, tv1) :: dss -> if(tv1 = tv) then typecheckDict ds
                                                                                              else failwith("wrong type: different value types in the dictionary")
                                                                    )
                                                      | _ -> failwith("wrong key type")
                                                    )
                            )
                            in typecheckDict dict)
            | Insert(k, v, d) -> (match teval d tenv with
                                | TDict(dd) -> (let tk = teval k tenv in
                                                (match tk with
                                                  | TString -> (match dd with
                                                                | [] -> TDict((tk, teval v tenv) :: [])
                                                                | (t1, tvalue) :: ds -> (let tv = teval v tenv in
                                                                                          (match (tvalue, tv) with
                                                                                           | (TBool, TBool) -> TDict((tk, tv) :: dd)
                                                                                           | (TInt, TInt) -> TDict((tk, tv) :: dd)
                                                                                           | (TString, TString) -> TDict((tk, tv) :: dd)
                                                                                           | (_, _) -> failwith("wrong type")
                                                                                           ))
                                                                )
                                                  | _ -> failwith("wrong key type")
                                                ))
                                | _ -> failwith("wrong type: not a dictionary")
                            )
            | Delete(d, k) -> (match teval d tenv with
                                | TDict(dd) -> (match teval k tenv with
                                                  | TString -> TDict(dd)
                                                  | _ -> failwith("wrong key type")
                                                )
                                | _ -> failwith("wrong type: not a dictionary")
                            )
                                                
            | Has_Key(k, d) -> (match teval d tenv with
                                | TDict(dd) -> (match teval k tenv with
                                                  | TString -> TBool
                                                  | _ -> failwith("wrong key type")
                                                )
                                | _ -> failwith("wrong type: not a dictionary")
                            )
            | Iterate(f, d) -> (match teval d tenv with     (*controllo che d sia effettivamente un dizionario*)
                                | TDict(dd) -> (match dd with
                                                  | [] -> TDict([])
                                                  | (t1, t2) :: ds -> (match teval f tenv with
                                                                        | FunT(t3, t4) -> (match (t2, t3, t4) with
                                                                                            | (TBool, TBool, TBool) -> TDict(dd)
                                                                                            | (TInt, TInt, TInt) -> TDict(dd)
                                                                                            | (TString, TString, TString) -> TDict(dd)
                                                                                            | (_, _, _) -> failwith("wrong function type")
                                                                                            )
                                                                        | _ -> failwith("wrong type: not a function")
                                                                        )
                                                )
                                | _ -> failwith("wrong type: not a dictionary")
                            )

            (* questo type checker per l'operazione primitiva Fold, funziona solo per valori del dizionario di tipo TInt e TBool *)
            | Fold(f, d) -> (match (teval d tenv) with
                                | TDict(dd) -> (match dd with
                                                  | [] -> TDict([])
                                                  | (t1, t2) :: ds -> (match teval f tenv with
                                                                        | BinFunT(tacc, ti, tres) -> (match (t2, ti) with
                                                                                            | (TInt, TInt) -> tacc    (*e tacc = tres dalla definizione di funzione binaria *)
                                                                                            | (TBool, TBool) -> tacc
                                                                                            | (_, _) -> failwith("wrong function type")
                                                                                            )
                                                                        | _ -> failwith("wrong type: not a function")
                                                                        )
                                                )
                                | _ -> failwith("wrong type: not a dictionary")
                            )

            | Filter(kl, d) -> (match teval d tenv with     (*controllo che d sia effettivamente un dizionario*)
                                | TDict(dd) -> if(checkKeyList kl tenv) then TDict(dd)
                                                else failwith("wrong list type")
                                | _ -> failwith("wrong type: not a dictionary"))


            (* valuta una variabile di tipo pairlist e restituisce una lista di tipo (tval*tval) list *)
            and tevalPairlist (pl : pairlist) (amb : tenv) : (tval * tval) list =
                      (match pl with
                        | Empty -> []
                        | Pair (k, v, l) -> (((teval k amb), (teval v amb)) :: (tevalPairlist l amb)) 
                      )
            (* restituisce true sse l è una lista di valori di tipo TString *)
            and checkKeyList l (amb : tenv) : bool = (match l with
                                    | [] -> true
                                    | x :: xs -> (match teval x amb with
                                                    | TString -> checkKeyList xs amb
                                                    | _ -> false )
                                    )
            ;;



(*--------------------QUALCHE TEST----------------------*)

let boolTest = teval (Ebool(true)) tenv0;;
let intTest = teval (Eint(4)) tenv0;;
let stringTest = teval (Estring("test")) tenv0;;

let binFunType = teval (TBinFun("acc", "arg", TInt, TInt, Sum(Den "acc", Sum(Den "arg", Eint(1))))) tenv0;;

let magazzinoFull = Dict(Pair(Estring("mele"), Eint(2), Pair(Estring("banane"), Eint(4), Pair(Estring("pere"), Eint(6), Pair(Estring("kiwi"), Eint(5), Empty)))));;
let dictTest = teval magazzinoFull tenv0;;

let insertTest = teval (Insert(Estring("fragole"), Eint(10), magazzinoFull)) tenv0;;

let deleteTest = teval (Delete(magazzinoFull, Estring("kiwi"))) tenv0;;

let iterateTest = teval (Iterate((TFun("x", TInt, Sum(Den "x", Eint(1)))), magazzinoFull)) tenv0;;

let foldTest = teval (Fold(TBinFun("acc", "x", TInt, TInt, Sum(Den "acc", Sum(Den "x", Eint 1))), magazzinoFull)) tenv0;;

let iterate_wrongArgumentInTheFunction = teval (Iterate((TFun("x", TBool, Ifthenelse(Den "x", Eint(1), Eint(0)))), magazzinoFull)) tenv0;; 