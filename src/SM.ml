open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
 *)
let rec eval env ((stack,((s,i,o) as sconf)) as conf) prg = match prg with
  | [] -> conf
  | JMP l :: _ -> eval env conf (env#labeled l)
  | CJMP (c, l) :: xs ->
     (match stack with
      | (a::b)    ->
          (match (a,c) with
           | (0,"z") -> eval env (b,sconf) (env#labeled l)
           | (i,"nz") when i <> 0 -> eval env (b,sconf) (env#labeled l)
           | _                  -> eval env (b,sconf) xs)
      | _         -> failwith "eval.CJMP: empty stack")
  | x :: xs ->
     let (s' : config) = match x with
       | CONST c -> (c :: stack, sconf)
       | BINOP op -> (match stack with
                        | (b::(a::c)) -> ((Language.Expr.evalbinop op a b)::c, sconf)
                        | _           -> failwith "eval.BINOP: less then 2 args on the stack")
       | READ -> (match i with
                    | (i0::ixs) -> (i0 :: stack, (s,ixs,o))
                    | _  -> failwith "eval.READ: input stream is empty")
       | WRITE -> (match stack with
                     | (a::xs) -> (stack,(s,i,o@[a]))
                     | _       -> failwith "eval.WRITE: can't read from stack")
       | LD y -> ((s y)::stack,sconf)
       | ST y -> (match stack with
                  | (a::xs) -> (xs, (Language.Expr.update y a s, i, o))
                  | _ -> failwith "eval.ST: stack is empty")
       | LABEL _ -> conf
       | _       -> failwith "sm eval: can't happen"
     in eval env s' xs

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile stmt0 =
  let mkl s n = "l_" ^ s ^ (string_of_int n)
  in let rec compileExpr e = match e with
          | Language.Expr.Const n -> [CONST n]
          | Language.Expr.Var x -> [LD x]
          | Language.Expr.Binop (op,x,y) -> compileExpr x @ compileExpr y @ [BINOP op]
  in let rec compileStmt n = function
     | Language.Stmt.Assign (x,e) -> (n, compileExpr e @ [ST x])
     | Language.Stmt.Read z -> (n, [READ;ST z])
     | Language.Stmt.Write e -> (n, compileExpr e @ [WRITE])
     | Language.Stmt.Seq (l,r) ->
        let (n1,l') = compileStmt n l in
        let (n2, r') = compileStmt n1 r in
        (n2, l' @ r')
     | Language.Stmt.Skip      -> (n, [])
     | Language.Stmt.If (e,l,r) ->
        let (n1, s1) = compileStmt n l in
        let l1 = mkl "if" n1 in
        let (n2, s2) = compileStmt (n1+1) r in
        let l2 = mkl "if" n2 in
        (n2+1, compileExpr e @ [CJMP ("z", l1)] @ s1 @ [JMP l2; LABEL l1] @ s2 @ [LABEL l2])
     | Language.Stmt.While (e,s) ->
        let l1 = mkl "wh" n in
        let (n', s') = compileStmt (n+1) s in
        let l2 = mkl "wh" n' in
        (n'+1, [JMP l2; LABEL l1] @ s' @ [LABEL l2] @ compileExpr e @ [CJMP ("nz", l1)])
     | Language.Stmt.Until (s,e) ->
        let l1 = mkl "unt" n in
        let (n', s') = compileStmt (n+1) s in
        (n', [LABEL l1] @ s' @ compileExpr e @ [CJMP ("z", l1)])

  in let (_, res) = compileStmt 0 stmt0
  in res
