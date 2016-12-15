module BI = Big_int_impl.BI

type num = BI.big_int

let zero = BI.zero_big_int
let succ = BI.succ_big_int
let pred = BI.pred_big_int
let pred_nat p =
  if BI.eq_big_int p BI.zero_big_int then
    BI.zero_big_int
  else
    BI.pred_big_int p
let negate = BI.minus_big_int

let add = BI.add_big_int
let sub = BI.sub_big_int
let sub_nat left right =
  if BI.gt_big_int right left then
    BI.zero_big_int
  else
    BI.sub_big_int left right
let mul = BI.mult_big_int
let pow_int = BI.power_big_int_positive_int
let pow_int_positive = BI.power_int_positive_int


let quomod = BI.quomod_big_int

let abs = BI.abs_big_int
let modulus = BI.mod_big_int
let div = BI.div_big_int

let min = BI.min_big_int
let max = BI.max_big_int

let less = BI.lt_big_int
let greater = BI.gt_big_int
let less_equal = BI.le_big_int
let greater_equal = BI.ge_big_int

let compare = BI.compare_big_int
let equal = BI.eq_big_int

let shift_left = BI.shift_left_big_int
let shift_right = BI.shift_right_big_int
let bitwise_or = BI.or_big_int
let bitwise_xor  = BI.xor_big_int
let bitwise_and = BI.and_big_int

let extract_num = BI.extract_big_int

let of_int = BI.big_int_of_int
let to_int = BI.int_of_big_int
let of_int32 = BI.big_int_of_int32
let to_int32 = BI.int32_of_big_int
let of_int64 = BI.big_int_of_int64
let to_int64 = BI.int64_of_big_int

let to_string = BI.string_of_big_int

let of_string = BI.big_int_of_string
let of_string_nat s =
  let i = of_string s in
    if BI.lt_big_int i BI.zero_big_int then
      assert false
    else
      i

let integerDiv_t = BI.div
let integerRem_t = fun x y -> BI.(mod) x y
let integerRem_f = fun x y -> BI.mod_big_int x y
