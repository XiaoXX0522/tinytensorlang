open Format
open Syntax
open Support.Error
open Support.Pervasive

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec isnumericval ctx t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | TmTag(_,l,t1,_) -> isval ctx t1
  | TmString _  -> true
  | TmUnit(_)  -> true
  | TmFloat _  -> true
  | t when isnumericval ctx t  -> true
  | TmAbs(_,_,_,_) -> true
  | TmRecord(_,fields) -> List.for_all (fun (l,ti) -> isval ctx ti) fields
  | TmTensor _ -> true
  | _ -> false

let rec eval1 ctx t = match t with
    TmIf(_,TmTrue(_),t2,t3) ->
      t2
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3
  | TmIf(fi,t1,t2,t3) ->
      let t1' = eval1 ctx t1 in
      TmIf(fi, t1', t2, t3)
  | TmTag(fi,l,t1,tyT) ->
      let t1' = eval1 ctx t1 in
      TmTag(fi, l, t1',tyT)
  | TmCase(fi,TmTag(_,li,v11,_),branches) when isval ctx v11->
      (try 
         let (x,body) = List.assoc li branches in
         termSubstTop v11 body
       with Not_found -> raise NoRuleApplies)
  | TmCase(fi,t1,branches) ->
      let t1' = eval1 ctx t1 in
      TmCase(fi, t1', branches)
  | TmApp(fi,TmAbs(_,x,tyT11,t12),v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(fi,v1,t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(fi, v1, t2')
  | TmApp(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(fi, t1', t2)
  | TmLet(fi,x,v1,t2) when isval ctx v1 ->
      termSubstTop v1 t2 
  | TmLet(fi,x,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmLet(fi, x, t1', t2) 
  | TmFix(fi,v1) as t when isval ctx v1 ->
      (match v1 with
         TmAbs(_,_,_,t12) -> termSubstTop t t12
       | _ -> raise NoRuleApplies)
  | TmFix(fi,t1) ->
      let t1' = eval1 ctx t1
      in TmFix(fi,t1')
  | TmVar(fi,n,_) ->
      (match getbinding fi ctx n with
          TmAbbBind(t,_) -> t 
        | _ -> raise NoRuleApplies)
  | TmAscribe(fi,v1,tyT) when isval ctx v1 ->
      v1
  | TmAscribe(fi,t1,tyT) ->
      let t1' = eval1 ctx t1 in
      TmAscribe(fi,t1',tyT)
  | TmRecord(fi,fields) ->
      let rec evalafield l = match l with 
        [] -> raise NoRuleApplies
      | (l,vi)::rest when isval ctx vi -> 
          let rest' = evalafield rest in
          (l,vi)::rest'
      | (l,ti)::rest -> 
          let ti' = eval1 ctx ti in
          (l, ti')::rest
      in let fields' = evalafield fields in
      TmRecord(fi, fields')
  | TmProj(fi, (TmRecord(_, fields) as v1), l) when isval ctx v1 ->
      (try List.assoc l fields
       with Not_found -> raise NoRuleApplies)
  | TmProj(fi, t1, l) ->
      let t1' = eval1 ctx t1 in
      TmProj(fi, t1', l)
  | TmTimesfloat(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 *. f2)
  | TmTimesfloat(fi,(TmFloat(_,f1) as t1),t2) ->
      let t2' = eval1 ctx t2 in
      TmTimesfloat(fi,t1,t2') 
  | TmTimesfloat(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmTimesfloat(fi,t1',t2) 
  | TmSucc(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmSucc(fi, t1')
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo)
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      nv1
  | TmPred(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmPred(fi, t1')
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      TmFalse(dummyinfo)
  | TmIsZero(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmIsZero(fi, t1')
  | TmAdd(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 +. f2)
  | TmAdd(fi,TmTensor(_,s1,d1),TmTensor(_,s2,d2)) ->
      let newdata = Array.map2 ( +. ) d1 d2 in
      TmTensor(fi, s1, newdata)
  | TmAdd(fi,TmFloat(_,f1),TmTensor(_,s2,d2)) ->
      let newdata = Array.map (fun ff -> ff +. f1) d2 in
      TmTensor(fi, s2, newdata)
  | TmAdd(fi,TmTensor(_,s1,d1),TmFloat(_,f2)) ->
      let newdata = Array.map (fun ff -> ff +. f2) d1 in
      TmTensor(fi, s1, newdata)
  | TmAdd(fi,(TmFloat _|TmTensor _ as t1), t2) ->
      let t2' = eval1 ctx t2 in
      TmAdd(fi,t1,t2')
  | TmAdd(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmAdd(fi,t1',t2) 
  | TmSub(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 -. f2)
  | TmSub(fi,TmTensor(_,s1,d1),TmTensor(_,s2,d2)) ->
      let newdata = Array.map2 ( -. ) d1 d2 in
      TmTensor(fi, s1, newdata)
  | TmSub(fi,TmTensor(_,s1,d1),TmFloat(_,f2)) ->
      let newdata = Array.map (fun ff -> ff -. f2) d1 in
      TmTensor(fi, s1, newdata)
  | TmSub(fi,(TmFloat _|TmTensor _ as t1), t2) ->
      let t2' = eval1 ctx t2 in
      TmSub(fi,t1,t2')
  | TmSub(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmSub(fi,t1',t2) 
  | TmTimes(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 *. f2)
  | TmTimes(fi,TmTensor(_,s1,d1),TmTensor(_,s2,d2)) ->
      let newdata = Array.map2 ( *. ) d1 d2 in
      TmTensor(fi, s1, newdata)
  | TmTimes(fi,TmFloat(_,f1),TmTensor(_,s2,d2)) ->
      let newdata = Array.map (fun ff -> ff *. f1) d2 in
      TmTensor(fi, s2, newdata)
  | TmTimes(fi,TmTensor(_,s1,d1),TmFloat(_,f2)) ->
      let newdata = Array.map (fun ff -> ff *. f2) d1 in
      TmTensor(fi, s1, newdata)
  | TmTimes(fi,(TmFloat _|TmTensor _ as t1), t2) ->
      let t2' = eval1 ctx t2 in
      TmTimes(fi,t1,t2')
  | TmTimes(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmTimes(fi,t1',t2)
  | TmDiv(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 /. f2)
  | TmDiv(fi,TmTensor(_,s1,d1),TmTensor(_,s2,d2)) ->
      let newdata = Array.map2 ( /. ) d1 d2 in
      TmTensor(fi, s1, newdata)
  | TmDiv(fi,TmTensor(_,s1,d1),TmFloat(_,f2)) ->
      let newdata = Array.map (fun ff -> ff /. f2) d1 in
      TmTensor(fi, s1, newdata)
  | TmDiv(fi,(TmFloat _|TmTensor _ as t1), t2) ->
      let t2' = eval1 ctx t2 in
      TmDiv(fi,t1,t2')
  | TmDiv(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmDiv(fi,t1',t2)
  | TmMatMult(fi,TmTensor(_,s1,d1),TmTensor(_,s2,d2)) ->
      let newshape = List.append (List.rev @@ List.tl @@ List.rev s1) (List.tl s2) in
      let newsize = Tensorhelper.prod newshape in 
      let newdata = Array.init newsize
        (fun idx -> 
          let lidx = Tensorhelper.fold_index newshape idx in
          let li1,li2 = Tensorhelper.split lidx ((List.length s1) - 1) in
          let iteri = Tensorhelper.range (List.hd s2) in 
          let iterprod = List.map 
            (fun ii -> 
              d1.(Tensorhelper.flat_index s1 (List.append li1 [ii]))
              *. d2.(Tensorhelper.flat_index s2 (ii :: li2)))
            iteri in
          Tensorhelper.sumf iterprod) in
      if newsize = 1 then TmFloat(fi,newdata.(0)) 
      else TmTensor(fi,newshape,newdata)
  | TmMatMult(fi,(TmTensor _ as t1), t2) ->
      let t2' = eval1 ctx t2 in
      TmMatMult(fi,t1,t2')
  | TmMatMult(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmMatMult(fi,t1',t2) 
  | TmProduct(fi,TmTensor(_,s1,d1),TmTensor(_,s2,d2)) ->
      let newshape = List.append s1 s2 in
      let newsize = Tensorhelper.prod newshape in 
      let newdata = Array.init newsize
        (fun idx -> 
          let lidx = Tensorhelper.fold_index newshape idx in
          let li1,li2 = Tensorhelper.split lidx (List.length s1) in
          d1.(Tensorhelper.flat_index s1 li1) *. d2.(Tensorhelper.flat_index s2 li2)) in
      TmTensor(fi,newshape,newdata)
  | TmProduct(fi,(TmTensor _ as t1), t2) ->
      let t2' = eval1 ctx t2 in
      TmProduct(fi,t1,t2')
  | TmProduct(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmProduct(fi,t1',t2) 
  | TmDirectsum(fi,t1,t2) ->
      pr "Needed to implement"; raise NoRuleApplies
  | TmAppend(fi,TmTensor(_,s1,d1),TmTensor(_,s2,d2)) ->
      let newshape = List.hd s1 + List.hd s2 :: List.tl s2 in
      let newdata = Array.append d1 d2 in
      TmTensor(fi,newshape,newdata)
  | TmContract(fi,i,j,t1) ->
      pr "Needed to implement"; raise NoRuleApplies
  | TmTrans(fi,i,j,t1) ->
      pr "Needed to implement"; raise NoRuleApplies
  | TmReshape(fi,ns,t1) ->
      pr "Needed to implement"; raise NoRuleApplies
  | _ -> 
      raise NoRuleApplies

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t

let evalbinding ctx b = match b with
    TmAbbBind(t,tyT) ->
      let t' = eval ctx t in 
      TmAbbBind(t',tyT)
  | bind -> bind

let istyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> true
  | _ -> false

let gettyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> tyT
  | _ -> raise NoRuleApplies

let rec computety ctx tyT = match tyT with
    TyVar(i,_) when istyabb ctx i -> gettyabb ctx i
  | _ -> raise NoRuleApplies

let rec simplifyty ctx tyT =
  try
    let tyT' = computety ctx tyT in
    simplifyty ctx tyT' 
  with NoRuleApplies -> tyT

let rec tyeqv ctx tyS tyT =
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyString,TyString) -> true
  | (TyUnit,TyUnit) -> true
  | (TyId(b1),TyId(b2)) -> b1=b2
  | (TyFloat,TyFloat) -> true
  | (TyVar(i,_), _) when istyabb ctx i ->
      tyeqv ctx (gettyabb ctx i) tyT
  | (_, TyVar(i,_)) when istyabb ctx i ->
      tyeqv ctx tyS (gettyabb ctx i)
  | (TyVar(i,_),TyVar(j,_)) -> i=j
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyBool,TyBool) -> true
  | (TyNat,TyNat) -> true
  | (TyRecord(fields1),TyRecord(fields2)) -> 
      List.length fields1 = List.length fields2
      &&                                         
      List.for_all 
        (fun (li2,tyTi2) ->
          try let (tyTi1) = List.assoc li2 fields1 in
              tyeqv ctx tyTi1 tyTi2
          with Not_found -> false)
        fields2
  | (TyVariant(fields1),TyVariant(fields2)) ->
      (List.length fields1 = List.length fields2)
      && List.for_all2
          (fun (li1,tyTi1) (li2,tyTi2) ->
              (li1=li2) && tyeqv ctx tyTi1 tyTi2)
          fields1 fields2
  | (TyTensor(shape1),TyTensor(shape2)) ->
      shape1 = shape2
  | _ -> false

(* ------------------------   TYPING  ------------------------ *)

let rec typeof ctx t =
  match t with
    TmInert(fi,tyT) ->
      tyT
  | TmTrue(fi) -> 
      TyBool
  | TmFalse(fi) -> 
      TyBool
  | TmIf(fi,t1,t2,t3) ->
     if tyeqv ctx (typeof ctx t1) TyBool then
       let tyT2 = typeof ctx t2 in
       if tyeqv ctx tyT2 (typeof ctx t3) then tyT2
       else error fi "arms of conditional have different types"
     else error fi "guard of conditional not a boolean"
  | TmCase(fi, t, cases) ->
      (match simplifyty ctx (typeof ctx t) with
         TyVariant(fieldtys) ->
           List.iter
             (fun (li,(xi,ti)) ->
                try let _ = List.assoc li fieldtys in ()
                with Not_found -> error fi ("label "^li^" not in type"))
             cases;
           let casetypes =
             List.map (fun (li,(xi,ti)) ->
                         let tyTi =
                           try List.assoc li fieldtys
                           with Not_found ->
                             error fi ("label "^li^" not found") in
                         let ctx' = addbinding ctx xi (VarBind(tyTi)) in
                         typeShift (-1) (typeof ctx' ti))
                      cases in
           let tyT1 = List.hd casetypes in
           let restTy = List.tl casetypes in
           List.iter
             (fun tyTi -> 
                if not (tyeqv ctx tyTi tyT1)
                then error fi "fields do not have the same type")
             restTy;
           tyT1
        | _ -> error fi "Expected variant type")
  | TmTag(fi, li, ti, tyT) ->
      (match simplifyty ctx tyT with
          TyVariant(fieldtys) ->
            (try
               let tyTiExpected = List.assoc li fieldtys in
               let tyTi = typeof ctx ti in
               if tyeqv ctx tyTi tyTiExpected
                 then tyT
                 else error fi "field does not have expected type"
             with Not_found -> error fi ("label "^li^" not found"))
        | _ -> error fi "Annotation is not a variant type")
  | TmVar(fi,i,_) -> getTypeFromContext fi ctx i
  | TmAbs(fi,x,tyT1,t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, typeShift (-1) tyT2)
  | TmApp(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match simplifyty ctx tyT1 with
          TyArr(tyT11,tyT12) ->
            if tyeqv ctx tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch"
        | _ -> error fi "arrow type expected")
  | TmLet(fi,x,t1,t2) ->
     let tyT1 = typeof ctx t1 in
     let ctx' = addbinding ctx x (VarBind(tyT1)) in         
     typeShift (-1) (typeof ctx' t2)
  | TmFix(fi, t1) ->
      let tyT1 = typeof ctx t1 in
      (match simplifyty ctx tyT1 with
           TyArr(tyT11,tyT12) ->
             if tyeqv ctx tyT12 tyT11 then tyT12
             else error fi "result of body not compatible with domain"
         | _ -> error fi "arrow type expected")
  | TmString _ -> TyString
  | TmUnit(fi) -> TyUnit
  | TmAscribe(fi,t1,tyT) ->
     if tyeqv ctx (typeof ctx t1) tyT then
       tyT
     else
       error fi "body of as-term does not have the expected type"
  | TmRecord(fi, fields) ->
      let fieldtys = 
        List.map (fun (li,ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)
  | TmProj(fi, t1, l) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRecord(fieldtys) ->
            (try List.assoc l fieldtys
             with Not_found -> error fi ("label "^l^" not found"))
        | _ -> error fi "Expected record type")
  | TmFloat _ -> TyFloat
  | TmTimesfloat(fi,t1,t2) ->
      if tyeqv ctx (typeof ctx t1) TyFloat
      && tyeqv ctx (typeof ctx t2) TyFloat then TyFloat
      else error fi "argument of timesfloat is not a number"
  | TmZero(fi) ->
      TyNat
  | TmSucc(fi,t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of succ is not a number"
  | TmPred(fi,t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of pred is not a number"
  | TmIsZero(fi,t1) ->
      if tyeqv ctx (typeof ctx t1) TyNat then TyBool
      else error fi "argument of iszero is not a number"
  | TmTensor(fi,shape,data) ->
      TyTensor(shape)
  | TmAdd(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyFloat,TyFloat) -> TyFloat
        | (TyTensor(s1),TyTensor(s2)) -> 
            if s1 = s2 then TyTensor(s1)
            else error fi "arguments' shapes do not match"
        | (TyFloat,TyTensor(s)) -> TyTensor(s)
        | (TyTensor(s),TyFloat) -> TyTensor(s)
        | (_,_) -> error fi "argument is neither a float nor a tensor")
  | TmSub(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyFloat,TyFloat) -> TyFloat
        | (TyTensor(s1),TyTensor(s2)) -> 
            if s1 = s2 then TyTensor(s1)
            else error fi "arguments' shapes do not match"
        | (TyTensor(s),TyFloat) -> TyTensor(s)
        | (_,_) -> error fi "argument is neither a float nor a tensor")
  | TmTimes(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyFloat,TyFloat) -> TyFloat
        | (TyTensor(s1),TyTensor(s2)) -> 
            if s1 = s2 then TyTensor(s1)
            else error fi "arguments' shapes do not match"
        | (TyFloat,TyTensor(s)) -> TyTensor(s)
        | (TyTensor(s),TyFloat) -> TyTensor(s)
        | (_,_) -> error fi "argument is neither a float nor a tensor")
  | TmDiv(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyFloat,TyFloat) -> TyFloat
        | (TyTensor(s1),TyTensor(s2)) -> 
            if s1 = s2 then TyTensor(s1)
            else error fi "arguments' shapes do not match"
        | (TyTensor(s),TyFloat) -> TyTensor(s)
        | (_,_) -> error fi "argument is neither a float nor a tensor")
  | TmMatMult(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyTensor(s1),TyTensor(s2)) -> 
            let size1,revrest1 = match List.rev s1 with a::b -> (a,b) | _ -> assert false in
            let size2,rest2 = match s2 with a::b -> (a,b) | _ -> assert false in
            if size1 = size2 then
              let newshape = List.append (List.rev revrest1) rest2 in
              if newshape = [] then TyFloat
              else TyTensor(newshape)
            else error fi "arguments' shapes do not match"
        | (_,_) -> error fi "argument is not a tensor")
  | TmProduct(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyTensor(s1),TyTensor(s2)) -> 
            let newshape = List.append s1 s2 in
            TyTensor(newshape)
        | (_,_) -> error fi "argument is not a tensor")
  | TmDirectsum(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyTensor(s1),TyTensor(s2)) -> 
            if List.length s1 = List.length s2 then
              let newshape = List.map2 ( + ) s1 s2 in
              TyTensor(newshape)
            else error fi "two tensor with different rank cannot be direct summed"
        | (_,_) -> error fi "argument is not a tensor")
  | TmAppend(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      let tyT1 = simplifyty ctx tyT1 in
      let tyT2 = simplifyty ctx tyT2 in 
      (match (tyT1,tyT2) with
          (TyTensor(s1),TyTensor(s2)) -> 
            let size1,rest1 = match s1 with a::b -> (a,b) | _ -> assert false in
            let size2,rest2 = match s2 with a::b -> (a,b) | _ -> assert false in
            if rest1 = rest2 then
              let newshape = (size1+size2)::rest1 in
              TyTensor(newshape)
            else error fi "append only concates the first dimension of tensors"
        | (_,_) -> error fi "argument is not a tensor")
  | TmContract(fi,i,j,t1) ->
      let tyT1 = typeof ctx t1 in
      let tyT1 = simplifyty ctx tyT1 in
      (match tyT1 with
          TyTensor(s1) -> 
            (if i = j then error fi "contraction on same dimension is not allowed" 
            else let i, j = (min i j), (max i j) in
            try if List.nth s1 (i-1) = List.nth s1 (j-1) then
                let rec dropij n = function
                  | [] -> []
                  | h :: t -> if n = i || n = j then dropij (n+1) t else h :: dropij (n+1) t in
                let newshape = dropij 1 s1 in
                if newshape = [] then TyFloat
                else TyTensor(newshape)
              else error fi "contraction on dimensions with different size is not allowed"
            with Invalid_argument _ | Failure _ -> error fi "contraction dimension out of range")
        | _ -> error fi "argument is not a tensor")
  | TmTrans(fi,i,j,t1) ->
      let tyT1 = typeof ctx t1 in
      let tyT1 = simplifyty ctx tyT1 in
      (match tyT1 with
          TyTensor(s1) -> 
            (if i = j then error fi "transpose on same dimension is not allowed" else
            try let newshape = Tensorhelper.swap s1 i j in
              TyTensor(newshape)
            with Invalid_argument _ | Failure _ -> error fi "transpose dimension out of range")
        | _ -> error fi "argument is not a tensor")
  | TmReshape(fi,ns1,t1) ->
      let tyT1 = typeof ctx t1 in
      let tyT1 = simplifyty ctx tyT1 in
      (match tyT1 with
          TyTensor(s1) -> 
            (if Tensorhelper.prod s1 = Tensorhelper.prod ns1 then TyTensor(ns1)
            else error fi "total size does not match")
        | _ -> error fi "argument is not a tensor")