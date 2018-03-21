(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
open Stdlib

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function
    | Int n -> n
    | _ -> failwith "int value expected"

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x =
      stringInit (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x =
      listInit (List.length a)   (fun j -> if j = i then x else List.nth a j)

    let rec showVal = function
      | (Int i) -> string_of_int i
      | (String s) -> "\"" ^ s ^ "\""
      | (Array a) -> "[" ^ String.concat ", " (List.map showVal a) ^ "]"

  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

    (* Empty state *)
    let empty = let e = fun x -> failwith ("can't resolve variable " ^ x)
                in { g = e; l = e; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)

    let update (x : string) (v : Value.t) (s : t) : t =
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

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t
    (* function call      *) | Call   of string * t list with show

    let rec showexpr = function
      | Const i -> string_of_int i
      | Var v   -> "var " ^ v
      | Binop (op,l,r) -> "(" ^ showexpr l ^ ") " ^ op ^" (" ^ showexpr r ^ ")"
      | Call (f,args) -> "call " ^ f ^ "(" ^ (foldl (fun s x -> s ^ showexpr x ^ ",") "" args) ^ ")"

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option


    let rec show_list = function
      | [] -> ""
      | x::[] -> string_of_int x
      | x::l -> string_of_int x ^ ", " ^ show_list l

    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)

    let evalbinop (op : string) (x0 : Value.t) (y0 : Value.t) : Value.t =
      match (x0,y0,op) with
      | (Int x, Int y,_) ->
         (let fromBool (b : bool) : int = if b then 1 else 0 in
          let toBool (i : int) = match i with
                 | 0 -> false
                 | _ -> true in
          let res = match op with
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
                 | o -> failwith (Printf.sprintf "eval: incorrect op: %s" o) in
          Int res)
      | (String s, Int i, _) -> failwith "TODO"
      | (Array s, Int i, _) -> failwith "TODO"

    let rec evalCall env conf f args eval =
      let (argVals,(st',i',o',_)) =
        foldl (fun (results,conf') e ->
               let ((_,_,_,vi) as conf'') = eval env conf' e
               in (fromSome vi :: results, conf''))
              ([], conf)
              args
      in (env#definition env f (List.rev argVals) (st',i',o',None))

    let rec eval env ((st,i,o,r) as conf : config) (e:t) : config =
      let retSame x = (st,i,o,Some x) in
      match e with
          | Const x -> retSame (Value.Int x)
          | Var v -> retSame (State.eval st v)
          | Binop (op, l, r) ->
             let ((_,_,_,l') as conf1) = eval env conf l in
             let ((st',i',o',r') as conf2) = eval env conf1 r in
             (st',i',o', Some (evalbinop op (fromSome l') (fromSome r')))
          | Call (f,args) -> evalCall env conf f args eval
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)

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

      pLeaf: fooname:IDENT "(" args:!(Util.list0 parse) ")" { Call (fooname,args) }
           | x:IDENT { Var x }
           | d:DECIMAL { Const d }
           | -"(" parse -")" ;

      pBinop: !(Ostap.Util.expr
        id
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
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list

    let rec printstmt = function
      | Assign (x,ix,v) ->
         "assign " ^ x ^ "ixs (" ^
                              (String.concat "," (List.map Expr.showexpr ix)) ^
                             ") to " ^ Expr.showexpr v
      | Seq _ -> "seq"
      | Skip -> "skip"
      | If (a,b,c) -> "if " ^ Expr.showexpr a ^ " " ^ printstmt b ^ " " ^ printstmt c
      | While (a,b) -> "while " ^ Expr.showexpr a ^ " " ^ printstmt b
      | Repeat _ -> "repeat"
      | Return t -> "return " ^ (match t with | None -> "none" | Some x -> Expr.showexpr x)
      | Call _ -> "call"

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          )
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st,i,o,r) as conf : Expr.config) k t : Expr.config =
      let rombeek s1 s2 = if s2 = Skip then s1 else Seq (s1,s2) in
      let curry f (a, b) = f a b in
      let dropr (st',i',o',r') = (st',i',o',None) in
      let posteval e f =
        (let (_,_,_,r') as c' = Expr.eval env conf e in
         let (c'', k',t') = f c' (fromSome r') in
         eval env c'' k' t') in
      let intfork i a b = match i with | (Value.Int 0) -> a
                                       | (Value.Int _) -> b
                                       | _ -> failwith "intfork" in
      match (k,t) with
      | (Skip, Skip) ->          conf
      | (_, Skip) ->             eval env (dropr conf) Skip k
      | (_, Assign (x, ixs, e)) -> posteval e @@ fun (st',i',o',_) r' -> (State.update x r' st',i',o',None),Skip,k
      | (_, Seq (l,r)) ->        eval env conf (rombeek r k) l
      | (_, If (e,l,r)) ->       posteval e @@ fun c r' -> dropr c, k, (intfork r' r l)
      | (_, While (e, t')) ->    posteval e @@ fun c r' -> (intfork r' (dropr c,Skip,k) (dropr c,rombeek t k, t'))
      | (_, Repeat (t', e)) ->   let conf' = eval env conf Skip t' in
                                 let (st',i',o',r') = Expr.eval env conf' e in
                                curry (eval env (st',i',o',None)) @@ (intfork (fromSome r') (k,t) (Skip,k))
      | (_, Call (func,args)) -> eval env (Expr.evalCall env conf func args Expr.eval) Skip k
      | (_, Return None) ->      conf
      | (_, Return (Some e)) ->  Expr.eval env conf e

    (* Statement parser *)
    ostap (
      parse: !(Ostap.Util.expr
               id
               [| `Righta, [ostap (";"), fun s1 s2 -> Seq (s1, s2)] |]
               pOne
              );
      pOne: multiIf
          | %"while" e:!(Expr.parse) %"do" s:parse %"od"             { While (e,s) }
          | %"for" init:parse "," cond:!(Expr.parse) "," upd:parse
            %"do" a:parse %"od"                                      { Seq (init,While(cond,Seq(a,upd))) }
          | %"repeat" s:parse %"until" e:!(Expr.parse)               { Repeat (s,e) }
          | %"return" e:(!(Expr.parse))?                             { Return e }
          | %"skip"                                                  { Skip }
          | x:IDENT ixs:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse) { Assign (x,ixs,e) }
          | fooname:IDENT "(" args:!(Util.list0 Expr.parse) ")"      { Call (fooname,args) }
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
  let module M = Map.Make (String) in
  let m          = foldl (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      = snd @@ M.find f m in
             let st'              = foldl (fun st (x, a) -> State.update x a st)
                                          (State.enter st (xs @ locs))
                                          (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
ostap (
  parse: d:(!(Definition.parse))* s:!(Stmt.parse) { (d,s) }
)
