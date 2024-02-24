

type nat =
| Z
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type lama_type =
| TName      of int
| TInt
| TString
| TArrow     of int list * lama_c * lama_type list * lama_type
| TArray     of lama_type
| TSexp      of (string * lama_type list) list

and lama_c =
| CTop
| CAnd   of lama_c * lama_c
| CEq    of lama_type * lama_type
| CBox   of lama_type
| CFun   of lama_type
| CInd   of lama_type * lama_type
| CIndI  of nat * lama_type * lama_type
| CSexp  of lama_type
| CSexpX of string * lama_type * lama_type list
| CCall  of lama_type * lama_type list * lama_type


let rec ent c c' =
    let cases = match c' with
    | CTop -> true
    | CAnd (l, r) -> ent c l && ent c r
    | CEq (l, r) -> l = r
    | CBox t -> (* TODO check Ind(t, s) *) ent c (CSexp t) || ent c (CFun t)
    | CFun (TName _) -> false (* TODO failwith *)
    | CFun  TInt -> false
    | CFun  TString -> false
    | CFun (TArrow _) -> true
    | CFun (TArray _) -> false
    | CFun (TSexp _) -> false
    | CInd (t1, t2) -> t1 = TString && t2 = TInt || t1 = TArray t2 (* TODO C-IndSexp *)
    | CIndI (i, t1, t2) -> ent c (CInd (t1, t2)) (* TODO C-IndISexp *)
    | CSexp (TName _) -> false (* TODO failwith *)
    | CSexp  TInt -> false
    | CSexp  TString -> false
    | CSexp (TArrow _) -> false
    | CSexp (TArray _) -> false
    | CSexp (TSexp _) -> true
    | CSexpX _ -> false (* TODO C-SexpX *)
    | CCall _ -> false (* TODO C-Call *)
    in

    (* C-AndL and C-AndR *)
    let and' = match c with
    | CAnd (l, r) -> ent l c' || ent r c'
    | CTop -> false
    | CEq _ -> false
    | CBox _ -> false
    | CFun _ -> false
    | CInd _ -> false
    | CIndI _ -> false
    | CSexp _ -> false
    | CSexpX _ -> false
    | CCall _ -> false
    in

    (* C-Refl *)
    c = c' || cases || and'
