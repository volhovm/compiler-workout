open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
let rec eval ((stack,((s,i,o) as sconf)) as conf) prg = match prg with
  | [] -> conf
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
     in eval s' xs

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt =
  let rec compileExpr e = match e with
          | Language.Expr.Const n -> [CONST n]
          | Language.Expr.Var x -> [LD x]
          | Language.Expr.Binop (op,x,y) -> compileExpr x @ compileExpr y @ [BINOP op]
  in match stmt with
     | Language.Stmt.Assign (x,e) -> compileExpr e @ [ST x]
     | Language.Stmt.Read z -> [READ;ST z]
     | Language.Stmt.Write e -> compileExpr e @ [WRITE]
     | Language.Stmt.Seq (l,r) -> compile l @ compile r
