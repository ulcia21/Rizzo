module Rizzo

type Channel = string

type Type =
    | TVar of string
    | TUnit
    | TPair of Type * Type
    | TSum of Type * Type
    | TFun of Type * Type
    | TExistsLater of Type //conceptually a pair of a clock theta and a suspended computation , that produces a value of type A as soon as theta ticks
    | TForallLater of Type
    | TSignal of Type //changes over time
    | TChannel of Type
    | TInt 

type Term =
    | Unit
    | TValue of Term
    | Ann of Term * Type
    | Var of string
    | Lambda of string * Term //applying function to variable, λx.t - a function that takes argument x and returns t.
    | App of Term * Term //function application t_1 t_2
    | Pair of Term * Term
    | Chan of Channel
    | Fst of Term //PI_1
    | Snd of Term //PI_2
    | Inl of Term //left
    | Inr of Term // right
    | Case of Term * (string * Term) * (string * Term)
    | ApplyLater of Term * Term //apply delayed function to delayed argument s(*)t (any clock ticks)
    | ApplyWhenV of Term * Term // apply function whenever v ticks f(>)v (connected to exists later)
    | Fix of string * Term //??
    | Delay of Term
    | Wait of Term
    | Watch of Term
    | Head of Term
    | Tail of Term
    | Sync of Term * Term //?
    | SignalCons of Term * Term // value, future value, signal constructor
    | Never 
    | Num of int
    | Add of Term * Term 

let rec isValue t =
    match t with
    | Unit -> true
    | Lambda _ -> true
    | Pair(v1,v2) when isValue v1 && isValue v2 -> true
    | Inl v when isValue v -> true
    | Inr v when isValue v -> true
    | Wait v when isValue v -> true
    | Watch v when isValue v -> true
    | SignalCons (v, w) when isValue v && isValue w -> true
    | ApplyWhenV (v,w) when isValue v && isValue w -> true 
    | Sync (v,w) when isValue v && isValue w -> true
    | Tail v when isValue v -> true
    | Delay _ -> true
    | Never -> true
    | _ -> false


let rec check env chanEnv te ty = 
    match te with
    | Unit -> ty = TUnit
    | Var x -> 
        match List.tryFind (fun (y,_)-> x=y) env with
        | Some (_, t) -> t = ty
        | None -> false 
    | Chan k ->
        match List.tryFind (fun (y,_)-> k=y) chanEnv with
        | Some (_, t) -> TChannel t = ty 
        | None -> false
    | Ann (t, typ) -> typ = ty && check env chanEnv t typ
    | Lambda (x, t) ->
        match ty with
        | TFun (a, b) -> check ((x,a)::env) chanEnv t b
        | _ -> false
    | App (t1,t2) ->
        match infer env chanEnv t2 with
        | Some a -> 
             check env chanEnv t1 (TFun(a,ty)) // the previous one worked when lambda was a second argument, this works when lambda is the first one
        | None -> false 
    | Pair (t1, t2) ->
        match ty with
        | TPair (a, b) -> check env chanEnv t1 a && check env chanEnv t2 b
        | _ -> false
    | Fst t -> 
        match infer env chanEnv t with
        | Some(TPair (a, _)) -> a=ty
        | _ -> false
    | Snd t -> 
        match infer env chanEnv t with 
        | Some(TPair (_, b)) -> b = ty
        | _ -> false
    | Inl t -> 
        match ty with 
        | TSum(a, _) -> check env chanEnv t a
        | _ -> false
    | Inr t -> 
        match ty with 
        | TSum(_, b) -> check env chanEnv t b
        | _ -> false
    | Case (t, (x, t1), (y, t2)) -> 
        match infer env chanEnv t with
        | Some (TSum(a,b)) ->
            check ((x,a)::env) chanEnv t1 ty &&
            check ((y,b)::env) chanEnv t2 ty
        | _ -> false
    | ApplyWhenV (w, v)-> 
        match infer env chanEnv w with
        | Some (TForallLater (TFun(a,b))) -> 
            ty = TExistsLater b && 
            check env chanEnv v (TExistsLater a)
        | _ -> false
    | ApplyLater (w, v) ->
        match infer env chanEnv w with
        | Some (TForallLater (TFun(a,b))) -> 
            ty = TForallLater b && 
            check env chanEnv v (TForallLater a)
        | _ -> false
    | Delay (t)-> 
        match ty with
        | TForallLater(a)-> check env chanEnv t a
        | _ -> false
    | Never ->
        match ty with
        | TExistsLater _ -> true
        | _ -> false
    | Head t ->
        match infer env chanEnv t with 
        | Some (TSignal a) -> a=ty
        | _ -> false
    | Tail t ->
        match infer env chanEnv t with 
        | Some (TSignal a) -> TExistsLater(TSignal a)=ty
        | _ -> false
    | Sync (t1, t2) ->
        match infer env chanEnv t1, infer env chanEnv t2 with
        | Some (TExistsLater a), Some (TExistsLater b) -> 
            ty = TExistsLater(TSum(TSum(a,b), TPair(a,b)))
        | _ -> false
    | SignalCons(s, t) ->
        match infer env chanEnv s with
        | Some a ->  check env chanEnv t (TExistsLater(TSignal a)) && ty = TSignal a
        | None -> false
    | Watch t ->
        match infer env chanEnv t with
        | Some (TSignal(TPair(a, TUnit))) -> ty = TExistsLater a
        | _ -> false
    | Wait t -> 
        match infer env chanEnv t with
        | Some (TChannel a) -> ty = TExistsLater a
        | _ -> false 
    | Fix (x,t) -> 
        match ty with 
        | a -> check ((x,TForallLater a)::env) chanEnv t a
    | Num _ -> ty = TInt
    | Add (s, t) -> 
        ty = TInt && check env chanEnv s TInt && check env chanEnv t TInt
    | _ -> false

// binding x.t means “This name refers to something inside this expression” so “inside t, x has a meaning”. So if we infer we do check what type has t, but t is dependant on x, but x has a type forall a, and that means a is waiting for a. So that would be slow/ineffecient? 
// and x in fix refers to everything that follows. So fix x.1 implies x=1, fix x.x+1 then x=x+1 and goes like this to infinity
// the real usage fix f. λn.
//    if n == 0 then 1
//    else n * f(n-1)
and infer env chanEnv te =
    match te with
    | Unit -> Some TUnit
    | Var x -> 
        match List.tryFind (fun (y,_) -> x = y) env with
        | Some (_, t)-> Some t
        | None -> None
    | Chan k -> 
        match List.tryFind (fun (y,_) -> k = y) chanEnv with
        | Some (_, t)-> Some (TChannel t)
        | None -> None
    | Ann (t, ty) ->
        if check env chanEnv t ty then Some ty else None
    | Pair (t1, t2) ->
        match infer env chanEnv t1, infer env chanEnv t2 with
        | Some a, Some b -> Some (TPair(a, b))
        | _ -> None
    | App (t1, t2) -> 
        match infer env chanEnv t1 with 
        | Some (TFun (a, b))  ->  
            if check env chanEnv t2 a then Some b else None
        | _ -> None
    | Fst t -> 
        match infer env chanEnv t with
        | Some (TPair(ta, _)) -> Some ta
        | _ -> None
    | Snd t -> 
        match infer env chanEnv t with
        | Some (TPair(_, tb)) -> Some tb
        | _ -> None
    | ApplyLater(w, v) ->
        match infer env chanEnv w with
        | Some (TForallLater (TFun(a,b))) -> 
            if check env chanEnv v (TForallLater a) then
                Some (TForallLater b)
            else None
        | _ -> None
    | ApplyWhenV (t1, t2) ->
        match infer env chanEnv t1 with
        | Some (TForallLater (TFun(a,b))) ->
            if check env chanEnv t2 (TExistsLater a) then
                Some (TExistsLater b)
            else None
        | _ -> None 
    | Delay t -> 
        match infer env chanEnv t with
        | Some a -> Some (TForallLater a)
        | _ -> None
    | Head t ->
        match infer env chanEnv t with 
        | Some (TSignal a) -> Some a
        | _ -> None 
    | Tail t -> 
        match infer env chanEnv t with 
        | Some (TSignal a) -> Some (TExistsLater(TSignal a))
        | _-> None
    | Sync (t1,t2)->
        match infer env chanEnv t1, infer env chanEnv t2 with
        | Some (TExistsLater a), Some (TExistsLater b) -> 
            Some (TExistsLater(TSum(TSum(a,b), TPair(a,b))))
        | _ -> None
    | SignalCons(s, t) ->
        match infer env chanEnv s with
        | Some a ->  
            match check env chanEnv t (TExistsLater(TSignal a)) with
            | true -> Some (TSignal a)
            | _ -> None
        | None -> None
    | Watch t -> 
        match infer env chanEnv t with
        | Some (TSignal(TPair(a, TUnit))) -> Some (TExistsLater a)
        | _ -> None
    | Wait t ->
        match infer env chanEnv t with
        | Some (TChannel a) -> Some (TExistsLater a)
        | _ -> None
    | Num _ -> Some TInt
    | Add (s, t) -> 
        match infer env chanEnv s, infer env chanEnv t with
        | Some TInt, Some TInt -> Some TInt
        | _ -> None
    | _ -> None

// no in, no lambda and Never in infer

type Env = (string * Type) list
type ChanEnv = (Channel *Type) list 

let env : Env = []
let chanEnv : ChanEnv = []
 
//checking if annotating lambda x->x works
let t1 = Ann(Lambda("x", Var "x"), TFun(TUnit, TUnit) )

let check1 = check env chanEnv t1 (TFun(TUnit, TUnit))
printfn "check1 = %b, and its supposed to be true" check1

let check2 = check env chanEnv t1 (TFun(TUnit, TVar "x"))
printfn "check2 = %b, and its supposed to be false" check2


//checking if app works 
let t2 = App( Ann(Lambda("x", Var "x"), TFun(TUnit, TUnit) ), Unit)
let infert2 = infer env chanEnv t2 
printfn "infert2 = %A, and its supposed to be Some TUnit" infert2

//using int 
let t3 = App( Ann(Lambda("x", Add (Var "x", Num 1)), TFun(TInt, TInt) ), Num 3)
let infert3 = infer env chanEnv t3 
printfn "infert3 = %A, and its supposed to be Some TInt" infert3
let check3 = check env chanEnv t3 TInt
printfn "check3 = %b, and its supposed to be true" check3

//mkSig
let rec mkSig da  = Lambda("a", SignalCons(Var "a", mkSig (Wait da)) ) //whenever da updates we construct the signal from a
// the type should be Exists A -> Exists Sig A
//not sure if that's it. Should I also annotate this thing?

//switch

//map
let map3 = Fix ("r",
                    Lambda ("f", 
                        Lambda ("s", 
                            App ( 
                                Lambda ("x", 
                                    App(
                                        Lambda ("xs",
                                            SignalCons(App (Var "f", Var "x"),
                                                ApplyWhenV (
                                                    ApplyLater(
                                                        Delay(
                                                            Lambda("r1", App(Var "r1", Var "f"))
                                                        ),
                                                    Var "r"), 
                                                Var "xs")
                                            )
                                        ) 
                                    , Tail (Var "s"))
                                ),
                            Head (Var "s") )
                        )
                    )
                )

let mapType =
    TFun(
        TFun(TUnit, TUnit),
        TFun(TSignal TUnit, TSignal TUnit)
    )

let mapAnnotated =
    Ann(map3, mapType)

let result = check env chanEnv mapAnnotated mapType
printfn "result of map3 = %b, and its supposed to be true" result



//fliter
