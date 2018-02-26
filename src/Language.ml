(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* State: a partial map from variables to integer values. *)
    type state = string -> int

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let evalbinop op x y =
         let fromBool (b : bool) : int = if b then 1 else 0 in
         let toBool (i : int) = match i with
                | 0 -> false
                | _ -> true
         in match op with
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

    (* Expression evaluator

          val eval : state -> t -> int

       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval (s:state) (e:t) : int = match e with
                | Const i -> i
                | Var v -> s v
                | Binop (op, l, r) ->
                  let matchOp (f : int -> int -> int) = f (eval s l) (eval s r)
                  in matchOp @@ evalbinop op

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
    *)
    ostap (
      parse: empty {failwith "Not yet implemented"}
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((s0,i,o) as s) t = match t with
              | Read x -> (Expr.update x (List.hd i) s0, List.tl i, o)
              | Write expr -> (s0, i, o @ [Expr.eval s0 expr])
              | Assign (x, expr) -> (Expr.update x (Expr.eval s0 expr) s0, i, o)
              | Seq (l,r) -> eval (eval s l) r

    (* Statement parser *)
    ostap (
      parse: empty {failwith "Not yet implemented"}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
