(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty = failwith "Not implemented"

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = failwith "Not implemented"

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = failwith "Not implemented"

    (* Creates a new scope, based on a given state *)
    let enter st xs = failwith "Not implemented"

    (* Drops a scope *)
    let leave st st' = failwith "Not implemented"

    let lookup st v = failwith "Not implemented"
  end

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
    let rec eval (s:State.t) (e:t) : int = match e with
                | Const i -> i
                | Var v -> State.lookup s v
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval ((s0,i,o) as s) t = match t with
              | Read x -> (State.update s0 x (List.hd i) s0, List.tl i, o)
              | Write expr -> (s0, i, o @ [Expr.eval s0 expr])
              | Assign (x, expr) -> (State.update s0 x (Expr.eval s0 expr) s0, i, o)
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

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: empty {failwith "Not implemented"}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = failwith "Not implemented"

(* Top-level parser *)
let parse = Stmt.parse
