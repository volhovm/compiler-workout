(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap.Util

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
            | "==" -> fromBool (x = y)
            | "!=" -> fromBool (x <> y)
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
    let mkBinop ops =
      List.map ( fun op -> ostap ($(op))
               , fun l r -> Binop (op, l, r))
               ops

    ostap (
      parse: pBinop | pLeaf;

      pLeaf: d:DECIMAL { Const d } | x:IDENT { Var x } | -"(" parse -")" | pBinop;

      pBinop: !(Ostap.Util.expr
        (fun x -> x)
        [|
          `Lefta, mkBinop ["!!"];
          `Lefta, mkBinop ["&&"];
          `Nona,  mkBinop ["<="; "<"; ">="; ">"; "!="; "=="];
          `Lefta, mkBinop ["+"; "-"];
          `Lefta, mkBinop ["*"; "/"; "%"]
        |]
        pLeaf)
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
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Until  of t * Expr.t

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
              | If (e,l,r) -> if Expr.eval s0 e <> 0 then eval s l else eval s r
              | While (e, t') -> if Expr.eval s0 e <> 0
                                 then eval s (Seq (t', t))
                                 else s
              | Until (t',e) ->
                 let ((s0',_,_) as s') = eval s t' in
                 if Expr.eval s0' e <> 0
                 then s'
                 else eval s' t
              | Skip -> s

    (* Statement parser *)
    ostap (
      parse: !(Ostap.Util.expr
               (fun x -> x)
               [| `Righta, [ostap (";"), fun s1 s2 -> Seq (s1, s2)] |]
               pOne
              );
      pOne: %"read" -"(" v:IDENT -")" { Read v }
          | %"write" -"(" e:!(Expr.parse) -")" { Write e }
          | multiIf
          | %"while" e:!(Expr.parse) %"do" s:parse %"od" { While (e,s) }
          | %"for" init:parse -"," cond:!(Expr.parse) -"," upd:parse %"do" a:parse %"od" { Seq (init,While(cond,Seq(a,upd))) }
          | %"repeat" s:parse %"until" e:!(Expr.parse) { Until (s,e) }
          | %"skip" { Skip }
          | v:IDENT -":=" e:!(Expr.parse) { Assign (v,e) };

      multiIf: %"if" i:nested %"fi" { i };
      nested: e:!(Expr.parse) %"then" s1:parse s2:multiIfElse { If (e, s1, s2) };
      multiIfElse: %"else" s2:parse { s2 }
                 | %"elif" n:nested { n }
                 | "" { Skip }

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
