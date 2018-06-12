let prod = fun lst -> List.fold_left ( * ) 1 lst

let sumf = fun lst -> List.fold_left ( +. ) 0. lst

let rec flat_index shape index = 
  match (shape, index) with
      (_, []) -> 0
    | (shd::stl, ihd::itl) -> (prod stl) * ihd + flat_index stl itl
    | ([], _::_) -> raise (Invalid_argument "index's dimension larger than tensor's")

let rec fold_index shape index = 
  if index >= prod shape then raise (Invalid_argument "index out of bounds") else
  match shape with
      [] -> raise (Invalid_argument "shape is empty list")
    | [l] -> [index] 
    | hd::tl -> let rshape = prod tl in index / rshape :: fold_index tl (index mod rshape)

let split list n =
  let rec aux i acc = function
    | [] -> List.rev acc, []
    | h :: t as l -> if i = 0 then List.rev acc, l
                       else aux (i-1) (h :: acc) t  in
  aux n [] list

let swap list i j = 
  List.mapi (fun idx ele -> match idx with 
                x when x = i-1 -> List.nth list (j-1) 
              | x when x = j-1 -> List.nth list (i-1)
              | _ -> ele) list

let rec range ?(start=0) len =
    if start >= len
    then []
    else start :: (range len ~start:(start+1))

type tensordata = 
  | Scalar of float
  | Vector of tensordata list

exception TensorBuildError of string

let rec check_shape : tensordata -> int list = function
  | Scalar f -> []
  | Vector (hd :: tl as tlst) -> 
      let hdsz = check_shape hd in
      if List.for_all (fun ele -> check_shape ele = hdsz) tl
        then List.length tlst :: hdsz
        else raise (TensorBuildError "Dimension size does not match.")
  | Vector [] -> raise (TensorBuildError "Dimension size is zero.")

let make_array tensordata = 
  let rec makeiter tdata tshape idx dst = match tdata with
    | Scalar f -> 
        dst.(idx) <- f
    | Vector tlst ->
        let rshape = List.tl tshape in
        let rsz = prod rshape in
        List.iteri (fun ii td -> makeiter td rshape (idx + (ii * rsz)) dst) tlst in
  let shape = check_shape tensordata in 
  let data = Array.create_float (prod shape) in 
  makeiter tensordata shape 0 data; data 