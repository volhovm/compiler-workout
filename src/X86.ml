(* X86 codegeneration interface *)

open Stdlib
open List

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)
(* Actually, 'allocate' is broken so 4 registers are used *)
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd =
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

let showopnd = function
  | (R i) -> Printf.sprintf "R %d" i
  | (S i) -> Printf.sprintf "S %d" i
  | (L i) -> Printf.sprintf "L %d" i
  | (M _) -> Printf.sprintf "M smth"

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string


(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl"
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | "xchg" -> "xchg"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "\n%s:" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)

let rec compile env code =
  (*print_prg code; Printf.eprintf "----------\n";*)
  let updenv (s,env') action = env', action s in
  let null x = Binop ("^", x, x) in
  let isreg x = match x with R _ -> true | _ -> false in
  let safeMov a b =
    if a = b then [] else
    if not (isreg a || isreg b) then [Mov (a,eax); Mov (eax,b)] else [Mov (a, b)] in
  let withreg x code' = if isreg x then code' x else [Mov (x,edx)] @ code' edx in
  let bind a1 a2 = fun env -> let (x,env') = a1 env in a2 env' in
  let tagToInt t = let l = (List.map Char.code @@ strToList t)
                   in (nth l 0) land 0xf0000 +
                      (nth l 1) land 0xf000 +
                      (nth l 2) land 0xf00 +
                      (nth l 3) land 0xf0 +
                      (nth l 4) land 0xf in
  let genCall env l n p =
       let ll = strToList l in
       let l = strFromList @@ match hd ll with | '.' -> 'B'::(tl ll) | _ -> ll in
       let push = fun x -> Push x in (* Because in ocaml constructors are not functions *)
       let passopnds, env' =
         if n == 0
         then [], env
         (* It receives args in the reversed order, as in stack -- head the newest *)
         else let modPush (toPush : opnd list) : opnd list = match l with
                | "Barray" -> (L n) :: toPush
                | "Bsta"   -> let x::v::is = toPush in [L (n-2); v; x] @ (rev is)
                | _ -> toPush in
              first (List.rev % modPush) (env#popMany n) in
       let passargs = map push passopnds in
       let pushedN = List.length passargs in
       let lreg = env'#live_registers in
       let saveregs = map push lreg in
       let restregs = rev @@ map (fun x -> Pop x) lreg in
       let cleanup = if pushedN == 0 then [] else [Binop ("+",L (pushedN*word_size),esp)] in
       let env'', retVar = if p then env', [] else updenv env'#allocate (fun s -> [Mov (eax, s)]) in
       env'', [Meta "#saving regs"] @
              saveregs @
              [Meta "#passing args"] @
              passargs @ [Meta "#calling"] @
              [Call l] @
              cleanup @
              [Meta "#restoring regs"] @
              restregs @
              [Meta "#retval"] @
              retVar in
  let compileStep env = function
    | CONST n         -> updenv env#allocate            @@ fun s -> [Mov (L n, s)]
    | LD x            -> updenv (env#global x)#allocate @@ fun s -> safeMov (env#loc x) s
    | ST x            -> updenv (env#global x)#pop      @@ fun s -> safeMov s (env#loc x)
    | LABEL l         -> env, [Label l]
    | JMP l           -> env, [Jmp l]
    | CJMP (s,l)      -> updenv (env#pop) @@ flip withreg @@ fun x -> [Binop ("!!", x, x); CJmp (s,l)]
    | CALL (l,n,p)    -> genCall env l n p
    | BEGIN (l,vr,ls) ->
       let env' = env#enter l vr ls in
       let prologue = [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ (env'#lsize)), esp)] in
       env', prologue
    | RET p           -> if p then updenv (env#pop) @@ fun s -> [Mov (s,eax); Jmp env#epilogue]
                         else env, [Jmp env#epilogue]
    | END             ->
       env,
       [Label (env#epilogue); Mov (ebp, esp); Pop ebp; Ret] @ (* epilogue *)
       (* ftp://ftp.gnu.org/old-gnu/Manuals/gas/html_chapter/as_7.html#SEC120 *)
       [Meta (Printf.sprintf "\t.set %s , %d" (env#lsize) (env#allocated * word_size))]
    | BINOP op ->
       let rhs, lhs, env' = env#pop2 in
       let newvar, env'' = env'#allocate in
       let binopCmp setArg =
         withreg rhs @@ fun x ->
         [null eax;
          Binop ("cmp", x, lhs);
          Set (setArg, "%al");
          Mov (eax, newvar)] in
       let convBin dest =
         [null eax;
          Binop ("cmp", eax, dest);
          Set ("NE", "%al");
          Mov (eax, dest)] in
       env'',
         (match op with
         | "+" | "-" | "*" -> withreg lhs (fun x -> Binop (op, rhs, x) :: safeMov x newvar)
         | "/" | "%"       -> [Mov (lhs, eax); Cltd; IDiv rhs; Mov ((if op = "/" then eax else edx), newvar)]
         | "<"  -> binopCmp "L"
         | "<=" -> binopCmp "LE"
         | ">"  -> binopCmp "G"
         | ">=" -> binopCmp "GE"
         | "==" -> binopCmp "E"
         | "!=" -> binopCmp "NE"
         | "&&" | "!!" -> convBin lhs @ convBin rhs @
                          withreg lhs (fun x -> [Binop (op, rhs, x); Mov (x, newvar)])
         | x -> failwith ("binop not supported: " ^ x))
    | STRING s        ->
       let s, env' = env#string s in
       let l, env'' = env'#allocate in
       let env''', call = genCall env'' ".string" 1 false in
       env''', (safeMov (M ("$" ^ s)) l) @ call
    | STA (y,n)       ->
       let s, env' = (env#global y)#allocate in
       second (fun c -> safeMov (env'#loc y) s @ c) @@ genCall env' ".sta" (n+2) true
    | DROP -> updenv (env#pop) @@ const []
    | DUP -> updenv (env#allocate) @@ fun s -> safeMov (env#peek) s
    | SWAP ->
       (env,
        let [x;y] = env#peek2 in
        let xch a b = [ Binop ("xchg", a, b) ] in
        match (isreg x, isreg y) with
        | (true,_) -> xch y x
        | (_,true) -> xch x y
        | _ -> safeMov x eax @ safeMov y x @ safeMov eax y)
    | TAG t ->
       let s, env' = env#allocate in
       second (fun c -> [Mov (L (tagToInt t), s)] @ c) (genCall env' ".tag" 1 false)
    | SEXP (t,n)      ->
       let s, env' = env#allocate in
       second (fun c -> [Mov (L (tagToInt t), s)] @ c) @@ genCall env' ".sexp" (n+1) true
    | ENTER vars -> failwith "ENTER not implemented, it's for HW12"
    | LEAVE -> failwith "LEAVE not implemented, it's for HW12"

  in (*Printf.eprintf "length of code: %d\n" (length code);*)
     foldl (fun (env,acc) i -> (*Printf.eprintf "%s\n" (SM.showi i);*)
                               second (fun x -> acc @ x) (compileStep env i))
           (env,[])
           code

(* A set of strings *)
module S = Set.Make (String)

(* A map indexed by strings *)
module M = Map.Make (String)

(* Environment implementation *)
let make_assoc l = combine l (listInit (length l) id)

class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)

    (* gets a name for a global variable *)
    method loc x =
      try S (- (assoc x args)  -  1)
      with Not_found ->
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)


    (* allocates a fresh position on a symbolic stack *)
    method allocate =
      let x, n =
        let rec allocate' = function
        | []                            -> ebx     , 0
        | (S n)::_                      -> S (n+1) , n+2
        | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (R n)::_                      -> S 0     , 1
        | _                             -> failwith "couldn't allocate"
        in
        allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = hd stack, {< stack = tl' "pop" stack >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    method popMany n = take n stack, {< stack = drop n stack >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}

    method peek = List.hd stack
    method peek2 = take 2 stack

    (* gets all global variables *)
    method globals = S.elements globals

    (* gets all string definitions *)
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots

    (* enters a function *)
    method enter f a l =
      {< stack_slots = length l;
         stack = [];
         locals = make_assoc l;
         args = make_assoc a;
         fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname

    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      filter (function R _ -> true | _ -> false) stack

  end

(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in
  let asm = Buffer.create 1024 in
  iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -g -F dwarf -o %s %s/runtime.o %s.s" name inc name)
