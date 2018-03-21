open GT
open Language
open Stdlib

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show

(* The type for the stack machine program *)
type prg = insn list

let showi i = show(insn) i
let print_prg p = List.iter (fun i -> Printf.eprintf "%s\n" (showi i)) p

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type econfig = State.t * int list * int list
type config = (prg * State.t) list * Value.t list * econfig

let printStack stack = Printf.eprintf "stack: %s\n" (showList Value.showVal stack)

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let splitRev n l = first List.rev @@ splitAt n l

let rec eval env ((cstack,(stack : Value.t list),((s,i,o) as sconf)) as conf) prg =
  (*printStack stack;
  (match prg with | x::_ -> Printf.eprintf ("Processing %s\n") (show(insn) x) | _ -> Printf.eprintf "");*)
  match prg with
  | [] -> conf
  | JMP l :: _ -> eval env conf (env#labeled l)
  | CALL (l,n,p) :: xs ->
     if (env#is_label l)
     then eval env ((xs,s)::cstack,stack,sconf) (env#labeled l)
     else eval env (env#builtin conf l n p) xs
  | END :: _ | RET _ :: _->
     (match cstack with
      | (nextcode,sprev)::cstack' ->
         eval env (cstack',stack,(State.leave s sprev,i,o)) nextcode
      | [] -> conf)
  | CJMP (c, l) :: xs ->
     (match stack with
      | (a::b)    ->
         let nconf = (cstack,b,sconf) in
          (match (a,c) with
           | (Value.Int 0,"z")              -> eval env nconf (env#labeled l)
           | (Value.Int i,"nz") when i <> 0 -> eval env nconf (env#labeled l)
           | (Value.Int _,_)                -> eval env nconf xs
           | _                              -> failwith "CJMP wrong type")
      | _         -> failwith "eval.CJMP: empty stack")
  | x :: xs ->
     let (c' : config) = match x with
       | CONST c -> (cstack, (Value.Int c) :: stack, sconf)
       | STRING s -> (cstack, (Value.String s) :: stack, sconf)
       | BINOP op -> (match stack with
                      | (b::a::c) -> let (s',i',o',r) = Language.Expr.evalBinop (s,i,o,None) op a b
                                     in (cstack, (fromSome r)::c, (s',i',o'))
                      | _           -> failwith "eval.BINOP: less then 2 args on the stack")
       | LD y -> (cstack,(State.eval s y)::stack,sconf)
       | ST y -> (match stack with
                  | (a::xs) -> (cstack, xs, (Language.State.update y a s, i, o))
                  | _ -> failwith @@ "eval.ST: stack is empty: " ^ y)
       | STA (y, n) -> (match stack with
                        | e::xs -> let (ixs,stack') = splitRev n xs
                                   in (cstack,stack',(Stmt.update s y e ixs,i,o))
                        | _ -> failwith "STA: stack didn't match")
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
          in (cstack,newstack, (newS,i,o))
       | SEXP (s,n) -> let (vals,stack') = splitAt n stack in
                       (cstack, Value.Sexp (s, (List.rev vals)) :: stack', sconf)
       | DROP -> (cstack, drop 1 stack, sconf)
       | DUP -> (cstack, (List.hd stack)::stack, sconf)
       | SWAP -> (cstack, (List.rev @@ take 2 stack) @ (drop 2 stack), sconf)
       | TAG s -> let x::stack' = stack in
                  let res = match x with | Value.Sexp (t,_) when t = s -> Value.Int 1
                                         | _ -> Value.Int 0 in
                  (cstack, res::stack', sconf)
       | ENTER v -> let (vals,stack') = splitAt (List.length v) stack in
                    let stmap = foldl (fun st (i,r) -> State.bind i r st)
                                      State.undefined
                                      (zip v (List.rev vals)) in
                    (cstack, stack', mod3_1 (fun st -> State.push st stmap v) sconf)
       | LEAVE -> (cstack, stack, mod3_1 State.drop sconf)

       | _       -> failwith "sm eval: can't happen"
     in eval env c' xs

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = splitRev n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           (*Printf.eprintf "Builtin: %s %B\n" f p;*)
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
open Language
let rec compile (defs,stmt0) : prg =
  (* Internal labels *)
  let mkl s n = "l_" ^ s ^ (string_of_int n) in
  (* External labels for compatibility (maybe they should be one) *)
  let lab s = "L" ^ s in
  let rec compileExpr e = match e with
          | Expr.Const n -> [CONST n]
          | Expr.String s -> [STRING s]
          | Expr.Array l ->
             concatMap compileExpr (List.rev l) @ [CALL (".array",List.length l,false)]
          | Expr.Var x -> [LD x]
          | Expr.Sexp (t,a) -> concatMap compileExpr a @ [SEXP (t,List.length a)]
          | Expr.Binop (op,x,y) -> compileExpr x @ compileExpr y @ [BINOP op]
          | Expr.Elem (a,ix) -> compileExpr ix @ compileExpr a @ [CALL (".elem",2,false)]
          | Expr.Length a -> compileExpr a @ [CALL (".length",1,false)]
          | Expr.Call (l,args) ->
            let (ax : prg) = concatMap compileExpr @@ List.rev args
            in ax @ [CALL (lab l, List.length args,false)] in
  let rec compileStmt n = function
     | Stmt.Assign (x,[],e) -> (n, compileExpr e @ [ST x])
     | Stmt.Assign (x,ixs,e) -> (n, concatMap compileExpr ixs @
                                             compileExpr e @
                                             [STA (x,List.length ixs)])
     | Stmt.Seq (l,r) ->
        let (n1,l') = compileStmt n l in
        let (n2, r') = compileStmt n1 r in
        (n2, l' @ r')
     | Stmt.Skip      -> (n, [])
     | Stmt.Return x ->
        (n, (match x with | None -> [] | Some y -> compileExpr y) @ [RET (x <> None)])
     | Stmt.If (e,l,r) ->
        let (n1, s1) = compileStmt n l in
        let l1 = "l_if" ^ (string_of_int n1) ^ "_1" in
        let (n2, s2) = compileStmt (n1+1) r in
        let l2 = "l_if" ^ (string_of_int n2) ^ "_2" in
        (n2+1, compileExpr e @ [CJMP ("z", l1)] @ s1 @ [JMP l2; LABEL l1] @ s2 @ [LABEL l2])
     | Stmt.While (e,s) ->
        let l1 = mkl "wh" n in
        let (n', s') = compileStmt (n+1) s in
        let l2 = mkl "wh" n' in
        (n'+1, [JMP l2; LABEL l1] @ s' @ [LABEL l2] @ compileExpr e @ [CJMP ("nz", l1)])
     | Stmt.Repeat (s,e) ->
        let l1 = mkl "rep" n in
        let (n', s') = compileStmt (n+1) s in
        (n', [LABEL l1] @ s' @ compileExpr e @ [CJMP ("z", l1)])
     | Stmt.Call (l,args) ->
        let (ax : prg) = List.concat @@ List.map compileExpr @@ List.rev args
        in (n, ax @ [CALL (lab l,List.length args,true)])
     | Stmt.Case (e,b) ->
        (* Yes, I've seen that there's "deriving foldl", but i have no idea how to use it *)
        let rec allVars = function
          | Stmt.Pattern.Wildcard -> []
          | Stmt.Pattern.Ident x -> [x]
          | Stmt.Pattern.Sexp (_,xs) -> concatMap allVars xs in
        let caseL i = "l_case_" ^ string_of_int n ^ "_" ^ string_of_int i in
        let lastCaseLabel = caseL (List.length b) in
        (* It doesn't compare array sizes, is it alright? *)
        (* No, really, .elem is unsafe, and we invoke it with some unchecked index i.... *)
        (* I could add "int" to TAG, but I'm not sure it is legal *)
        let rec genMatch inext = function
          | Stmt.Pattern.Wildcard -> [DROP]
          | Stmt.Pattern.Ident _ -> [DROP]
          | Stmt.Pattern.Sexp (t,xs) ->
             let guard = CJMP ("z", caseL inext) in
             (* I'm not sure that we need swap here... *)
             let eachChild i = function
               | (Stmt.Pattern.Sexp _ as pat) ->
                  [DUP; CONST i; SWAP; CALL (lab ".elem", 2, false)] @ genMatch inext pat
               (* We don't have to do it if pat is wildcard or ident *)
               | _ -> [] in
             let llen = List.length xs in
             (* check if tag matches *)
             let tagMatches = [ DUP; TAG t; guard ] in
             (* check if array length matches expected one *)
             let arrayLenMatches =
               if llen == 0
               then []
               else [ DUP;
                      CALL (lab ".length", 1, false);
                      CONST llen;
                      BINOP "==";
                      guard ] in
             tagMatches @
             arrayLenMatches @
             concatMap (uncurry eachChild) (zip (buildList 0 (llen-1)) xs)
               (* [ DROP ] *)
        (* value on top of stack is useful one *)
        in let rec genBind = function
             (* but we don't need it *)
             | Stmt.Pattern.Wildcard -> [DROP]
             (* we'd like to save it, so swap with previous one *)
             | Stmt.Pattern.Ident x -> [SWAP]
             | Stmt.Pattern.Sexp (_,xs) ->
                let eachChild i pat =
                  [DUP; CONST i; SWAP; CALL (lab ".elem", 2, false)] @ genBind pat in
                let children = concatMap (uncurry eachChild)
                                         (zip (buildList 0 (List.length xs - 1)) xs) in
                [DUP] @ children @ [DROP] in
        let rec genBranch i n' = function
          | (p,bi)::xs ->
             let cl = if i = 0 then [] else [ LABEL (caseL i) ] in
             let (n'',body) = compileStmt (n+1) bi in
             let (lastN, cont) = genBranch (i+1) n'' xs in
             (lastN, concat [ cl
                            ; [LABEL (mkl "DEBUG_MATCH_START_" n')]
                            ; genMatch (i+1) p
                            ; [LABEL (mkl "DEBUG_MATCH_END_" n')]
                            ; genBind p
                            ; [LABEL (mkl "DEBUG_BIND_END_" n')]
                            ; [ ENTER (allVars p) ]
                            ; [ DROP ] (* Drop matching variable *)
                            ; body
                            ; [ LEAVE ]
                            ; [ JMP lastCaseLabel ]
                            ; cont ])
          | _ -> (n', []) in
        let (n', branchesCode) = genBranch 0 (n+1) b in
        (n', compileExpr e @ branchesCode @ [LABEL lastCaseLabel])
     in let rec compileDef n (fname,(args,locals,body)) =
        let (n', c) = compileStmt n body in
        let fname = "L" ^ fname in
        (n', [LABEL fname; BEGIN (fname,args, locals)] @ c @ [END])

  in let (_, res) =
       List.fold_left (fun (n,c) d -> let (n',c') = compileDef n d in (n',c @ c'))
                      (let (n,c) = compileStmt 0 stmt0 in (n,c@[END]))
                      defs
  in res
