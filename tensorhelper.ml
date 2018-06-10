  let prod = fun lst -> List.fold_left ( * ) 1 lst

  let rec calc_index shape index = 
    match (shape, index) with
        (_, []) -> 0
      | (shd::stl, ihd::itl) -> shd * ihd + calc_index stl itl
      | (_, _::_) -> raise (Invalid_argument "index's dimension larger than tensor's")

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