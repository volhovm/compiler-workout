(* Simple expressions: syntax and semantics *)

open GT

@type expr =
  | Const of int
  | Var   of string
  | Binop of string * expr * expr with show

(* Available binary operators:
    !!                   --- disjunction
    &&                   --- conjunction
    ==, !=, <=, <, >=, > --- comparisons
    +, -                 --- addition, subtraction
    *, /, %              --- multiplication, division, reminder
*)

type state = string -> int

let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

let update (x:string) (v:int) (s:state) = fun y -> if x = y then v else s y

let rec eval (s:state) (e:expr) =
  match e with
  | Const i -> i
  | Var v -> s v
  | Binop (op, l, r) ->
     (* omg these nested 'let's are terrible, how about 'where'? non-monadic do notation? :\ *)
     let matchOp (f : int -> int -> int) = f (eval s l) (eval s r) in
     let fromBool (b : bool) : int = if b then 1 else 0 in
     let toBool (i : int) = match i with
            | 0 -> false
            | _ -> true
     in matchOp @@
          fun x y -> match op with
                     | "+" -> x + y
                     | "-" -> x - y
                     | "*" -> x * y
                     | "/" -> x / y
                     | "%" -> x mod y
                     | "<"  -> fromBool (x < y)
                     | "<=" -> fromBool (x <= y)
                     | ">"  -> fromBool (x > y)
                     | ">=" -> fromBool (x >= y)
                     | "==" -> fromBool (x == y)
                     | "!=" -> fromBool (x != y)
                     | "&&" -> fromBool (toBool x && toBool y)
                     | "!!" -> fromBool (toBool x || toBool y)
                     | x -> failwith (Printf.sprintf "eval: incorrect op: %s" x)
