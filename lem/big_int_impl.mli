module BI :
  sig
    type big_int
    val zero_big_int : big_int
    val unit_big_int : big_int
    val minus_big_int : big_int -> big_int
    val abs_big_int : big_int -> big_int
    val add_big_int : big_int -> big_int -> big_int
    val succ_big_int : big_int -> big_int
    val add_int_big_int : int -> big_int -> big_int
    val sub_big_int : big_int -> big_int -> big_int
    val pred_big_int : big_int -> big_int
    val mult_big_int : big_int -> big_int -> big_int
    val mult_int_big_int : int -> big_int -> big_int
    val square_big_int : big_int -> big_int
    val sqrt_big_int : big_int -> big_int
    val quomod_big_int : big_int -> big_int -> big_int * big_int
    val div_big_int : big_int -> big_int -> big_int
    val mod_big_int : big_int -> big_int -> big_int
    val gcd_big_int : big_int -> big_int -> big_int
    val power_int_positive_int : int -> int -> big_int
    val power_big_int_positive_int : big_int -> int -> big_int
    val power_int_positive_big_int : int -> big_int -> big_int
    val power_big_int_positive_big_int : big_int -> big_int -> big_int
    val sign_big_int : big_int -> int
    val compare_big_int : big_int -> big_int -> int
    val eq_big_int : big_int -> big_int -> bool
    val le_big_int : big_int -> big_int -> bool
    val ge_big_int : big_int -> big_int -> bool
    val lt_big_int : big_int -> big_int -> bool
    val gt_big_int : big_int -> big_int -> bool
    val max_big_int : big_int -> big_int -> big_int
    val min_big_int : big_int -> big_int -> big_int
    val num_digits_big_int : big_int -> int
    val string_of_big_int : big_int -> string
    val big_int_of_string : string -> big_int
    val big_int_of_int : int -> big_int
    val is_int_big_int : big_int -> bool
    val int_of_big_int : big_int -> int
    val big_int_of_int32 : int32 -> big_int
    val big_int_of_nativeint : nativeint -> big_int
    val big_int_of_int64 : int64 -> big_int
    val int32_of_big_int : big_int -> int32
    val nativeint_of_big_int : big_int -> nativeint
    val int64_of_big_int : big_int -> int64
    val float_of_big_int : big_int -> float
    val and_big_int : big_int -> big_int -> big_int
    val or_big_int : big_int -> big_int -> big_int
    val xor_big_int : big_int -> big_int -> big_int
    val shift_left_big_int : big_int -> int -> big_int
    val shift_right_big_int : big_int -> int -> big_int
    val shift_right_towards_zero_big_int : big_int -> int -> big_int
    val extract_big_int : big_int -> int -> int -> big_int
    val div : big_int -> big_int -> big_int
    val (mod) : big_int -> big_int -> big_int
  end

