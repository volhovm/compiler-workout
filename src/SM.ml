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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show

(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.eprintf "%s\n" (show(insn) i)) p

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

let printStack stack = Printf.eprintf "stack: %s\n" (Language.Expr.show_list stack)

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let rec eval env ((cstack,stack,((s,i,o,r) as sconf)) as conf) prg =
  (*printStack stack;*)
  (*(match prg with | x::_ -> Printf.eprintf ("Processing %s\n") (show(insn) x) | _ -> Printf.eprintf "");*)
  match prg with
  | [] -> conf
  | JMP l :: _ -> eval env conf (env#labeled l)
  | CALL (l,_,_) :: xs ->
     eval env ((xs,s)::cstack,stack,sconf) (env#labeled l)
  | END :: _ ->
     (match cstack with
      | (nextcode,sprev)::cstack' ->
         eval env (cstack',stack,(State.leave s sprev,i,o,r)) nextcode
      | [] -> conf)
  | CJMP (c, l) :: xs ->
     (match stack with
      | (a::b)    ->
         let nconf = (cstack,b,sconf) in
          (match (a,c) with
           | (0,"z") -> eval env nconf (env#labeled l)
           | (i,"nz") when i <> 0 -> eval env nconf (env#labeled l)
           | _                  -> eval env nconf xs)
      | _         -> failwith "eval.CJMP: empty stack")
  | x :: xs ->
     let (s' : config) = match x with
       | CONST c -> (cstack, c :: stack, sconf)
       | BINOP op -> (match stack with
                        | (b::(a::c)) -> (cstack, (Language.Expr.evalbinop op a b)::c, sconf)
                        | _           -> failwith "eval.BINOP: less then 2 args on the stack")
       | READ -> (match i with
                    | (i0::ixs) -> (cstack, i0 :: stack, (s,ixs,o,r))
                    | _  -> failwith "eval.READ: input stream is empty")
       | WRITE ->
          (match stack with
                     | (a::xs) -> (cstack, xs,(s,i,o@[a],r))
                     | _       -> failwith "eval.WRITE: can't read from stack")
       | LD y -> (cstack,(State.eval s y)::stack,sconf)
       | ST y -> (match stack with
                  | (a::xs) -> (cstack, xs, (Language.State.update y a s, i, o, r))
                  | _ -> failwith "eval.ST: stack is empty")
       | LABEL _ -> conf
       | BEGIN (_,vars,locals) ->
          let rec zip' acc = (function
                               | (st,[]) -> st, acc
                               | ([],_) -> failwith "BEGIN: stack is too empty"
                               | (st::stx,vr::vrx) -> zip' ((st,vr) :: acc) (stx, vrx)) in
          let newstack,assocVars = zip' [] (stack, vars) in
          let newS = List.fold_left (fun s' (v,x) -> State.update x v s')
                                    (State.enter s (vars @ locals))
                                    assocVars
          in (cstack,newstack, (newS,i,o,r))
       | _       -> failwith "sm eval: can't happen"
     in eval env s' xs

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run (p : prg) (i : int list) : int list =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o, _)) =
    eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [], Some 12345)) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile (defs,stmt0) : prg =
  let mkl s n = "l_" ^ s ^ (string_of_int n)
  in let rec compileExpr e = match e with
          | Language.Expr.Const n -> [CONST n]
          | Language.Expr.Var x -> [LD x]
          | Language.Expr.Binop (op,x,y) -> compileExpr x @ compileExpr y @ [BINOP op]
          | Language.Expr.Call (l,args) ->
            let (ax : prg) = List.concat @@ List.map compileExpr @@ List.rev args
            in ax @ [CALL ("fun_" ^ l,failwith "todo",failwith "todo")]
  in let rec compileStmt n = function
     | Language.Stmt.Assign (x,e) -> (n, compileExpr e @ [ST x])
     | Language.Stmt.Read z -> (n, [READ;ST z])
     | Language.Stmt.Write e -> (n, compileExpr e @ [WRITE])
     | Language.Stmt.Seq (l,r) ->
        let (n1,l') = compileStmt n l in
        let (n2, r') = compileStmt n1 r in
        (n2, l' @ r')
     | Language.Stmt.Skip      -> (n, [])
     | Language.Stmt.Return x -> (n, (match x with | None -> [] | Some y -> compileExpr y) @ [END])
     | Language.Stmt.If (e,l,r) ->
        let (n1, s1) = compileStmt n l in
        let l1 = "l_if" ^ (string_of_int n1) ^ "_1" in
        let (n2, s2) = compileStmt (n1+1) r in
        let l2 = "l_if" ^ (string_of_int n2) ^ "_2" in
        (n2+1, compileExpr e @ [CJMP ("z", l1)] @ s1 @ [JMP l2; LABEL l1] @ s2 @ [LABEL l2])
     | Language.Stmt.While (e,s) ->
        let l1 = mkl "wh" n in
        let (n', s') = compileStmt (n+1) s in
        let l2 = mkl "wh" n' in
        (n'+1, [JMP l2; LABEL l1] @ s' @ [LABEL l2] @ compileExpr e @ [CJMP ("nz", l1)])
     | Language.Stmt.Repeat (s,e) ->
        let l1 = mkl "rep" n in
        let (n', s') = compileStmt (n+1) s in
        (n', [LABEL l1] @ s' @ compileExpr e @ [CJMP ("z", l1)])
     | Language.Stmt.Call (l,args) ->
        let (ax : prg) = List.concat @@ List.map compileExpr @@ List.rev args
        in (n, ax @ [CALL ("fun_" ^ l,failwith "todo",failwith "todo")])
     in let rec compileDef n (fname,(args,locals,body)) =
        let (n', c) = compileStmt n body in
        (n', [LABEL ("fun_" ^ fname); BEGIN (failwith "todo",args, locals)] @ c @ [END])

  in let (_, res) =
       List.fold_left (fun (n,c) d -> let (n',c') = compileDef n d in (n',c @ c'))
                      (let (n,c) = compileStmt 0 stmt0 in (n,c@[END]))
                      defs
  in res
