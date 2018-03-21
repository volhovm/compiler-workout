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
    let empty = let e = fun x -> failwith ("can't resolve variable " ^ x)
                in { g = e; l = e; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)

    let update (x : string) (v : int) (s : t) : t =
      let upd fallback = fun y -> if y = x then v else fallback y in
      if List.mem x s.scope
          then { s with l = upd s.l }
          else { s with g = upd s.g }

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if List.mem x s.scope then s.l x else s.g x

    (* Creates a new scope, based on a given state *)
    let enter s xs = { empty with g = s.g; scope = xs }

    (* Drops a scope *)
    let leave sinner souter = { souter with g = sinner.g }
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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
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

    let rec eval (s:State.t) (e:t) : int = match e with
                | Const i -> i
                | Var v -> State.eval s v
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
      parse: pBinop;

      pLeaf: x:IDENT { Var x } | d:DECIMAL { Const d } | -"(" parse -")" ;

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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show


    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    let rec eval env ((s0,i,o,r) as s : Expr.config) k t = match t with
              | Read x -> (State.update x (List.hd i) s0, List.tl i, o, r)
              | Write expr -> (s0, i, o @ [Expr.eval s0 expr], r)
              | Assign (x, expr) -> (State.update x (Expr.eval s0 expr) s0, i, o, r)
              | Seq (l,r) -> eval env (eval env s k l) k r
              | If (e,l,r) -> eval env s k (if Expr.eval s0 e <> 0 then l else r)
              | While (e, t') -> if Expr.eval s0 e <> 0
                                 then eval env s k (Seq (t', t))
                                 else s
              | Repeat (t',e) ->
                 let ((s0',_,_,_) as s') = eval env s k t' in
                 if Expr.eval s0' e <> 0
                 then s'
                 else eval env s' k t
              | Skip -> s
              | Call (func,argVals) ->
                 let (args,locals,body) = env func in

                 if List.length args != List.length argVals
                 then failwith "can't call function: number of args do not match"
                 else
                 (* new state with local vars assigned *)
                 let sinner : State.t =
                   List.fold_left
                     (fun s (x,v) -> State.update x (Expr.eval s0 v) s)
                     (State.enter s0 (args @ locals))
                     (List.combine args argVals) in
                 let (s',i',o',_) =
                   eval env (sinner,i,o,r) k body in
                 (State.leave s' s0,i',o', r)

    (* Statement parser *)
    ostap (
      parse: !(Ostap.Util.expr
               (fun x -> x)
               [| `Righta, [ostap (";"), fun s1 s2 -> Seq (s1, s2)] |]
               pOne
              );
      pOne: %"read" "(" v:IDENT ")" { Read v }
          | %"write" "(" e:!(Expr.parse) ")" { Write e }
          | multiIf
          | %"while" e:!(Expr.parse) %"do" s:parse %"od" { While (e,s) }
          | %"for" init:parse -"," cond:!(Expr.parse) -"," upd:parse %"do" a:parse %"od" { Seq (init,While(cond,Seq(a,upd))) }
          | %"repeat" s:parse %"until" e:!(Expr.parse) { Repeat (s,e) }
          | %"skip" { Skip }
          | x:IDENT n:( ":=" e:!(Expr.parse)               { Assign (x,e) }
                      | "(" e:!(Util.list0 Expr.parse) ")" { Call (x,e) } )
                    {n}
          ;

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
      parse: %"fun" i:IDENT "(" v:ids ")" l:locals "{" b:!(Stmt.parse) "}" { (i,(v,l,b)) };
      locals: x:(%"local" ids)? { match x with None -> [] | Some x -> x };
      ident: IDENT;
      ids: !(Util.list0 ident)
    )
  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval ((defs, body) : t) (i : int list) : int list =
  let (_,_,o,_) = Stmt.eval (fun x -> List.assoc x defs) (State.empty,i,[], Some 12345) 12345 body
  in o

(* Top-level parser *)
ostap (
  parse: d:(!(Definition.parse))* s:!(Stmt.parse) { (d,s) }
)
