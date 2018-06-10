type tensordata = 
  | Scalar of float
  | Vector of tensordata list

exception TensorBuildError of string

let rec checkshape : tensordata -> int list = function
  | Scalar f -> []
  | Vector (hd :: tl as tlst) -> 
      let hdsz = checkshape hd in
      if List.for_all (fun ele -> checkshape ele = hdsz) tl
        then List.length tlst :: hdsz
        else raise (TensorBuildError "Dimension size does not match.")
  | Vector [] -> raise (TensorBuildError "Dimension size is zero.")

let prod = fun lst -> List.fold_left ( * ) 1 lst

let makearray tensordata = 
  let rec makeiter tdata tshape idx dst = match tdata with
    | Scalar f -> 
        dst.(idx) <- f
    | Vector tlst ->
        let rshape = List.tl tshape in
        let rsz = prod rshape in
        List.iteri (fun ii td -> makeiter td rshape (idx + (ii * rsz)) dst) tlst in
  let shape = checkshape tensordata in 
  let data = Array.make_float (prod shape) in 
  makeiter tensordata shape 0 data; data 