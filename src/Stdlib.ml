(* Module for functions that should be in prelude, but for some reason they are not *)
(* And also some utility functions *)

open List

let flip x a b = x b a
let id x = x
let foldl = fold_left
let foldr = fold_right
let swap (a,b) = (b,a)
let const x = fun _ -> x
(* Composition... *)
let (%) a b = fun x -> a (b x)
let zip = List.combine

let curry f a b = f (a,b)
let uncurry f (a, b) = f a b

(* that's a parody of bifunctors, right *)
let second f (a,b) = (a,f b)
let first f (a,b) = (f a,b)

(* fromMaybe *)
let fromSome = function | Some x -> x | None -> failwith "fromRes: failed to resolve None"
let someToList = function | Some x -> x | None -> []

let tl' s = function
      | [] -> failwith ("tl': " ^ s)
      | (_::xs) -> xs
let rec drop n l = if n == 0 then l else drop (n-1) (tl l)
let rec take n l = if n == 0 then [] else hd l :: take (n-1) (tl l)
let dropEnd n = List.rev % drop n % List.rev

let splitAt n l = (take n l, drop n l)

(* Yes, that's right -- no [a..b] notation :joy: *)
let rec buildList a b = if a < b
                        then a::(buildList (a+1) b)
                        else if a == b then [a] else []

(* Because i don't know how to upgrade ocaml to make List.init available :shrug: *)
let listInit len f = List.map f (buildList 0 (len - 1))

let concat = List.concat
let concatMap f = List.concat % List.map f

let strToList (s : string) : (char list) =
    List.map (String.get s) (buildList 0 (String.length s - 1))
let strFromList (l : char list) : string =
    String.concat "" (List.map (String.make 1) l)

let strDrop n = strFromList % drop n % strToList
let strTake n = strFromList % take n % strToList

(* Same problem as with listInit *)
let stringInit (len : int) (f : int -> char) =
    String.concat "" (List.map (String.make 1 % f) (buildList 0 (len - 1)))

let time s f x =
    let t = Sys.time() in
    let fx = f x in
    Printf.eprintf "Time of %s: %fs\n" s (Sys.time() -. t);
    fx

let showList f l = "[" ^ (String.concat ", " (List.map f l)) ^ "]"
let showIntList = showList string_of_int


(* Lens. LENS. L E  N        S    !! !  ! 1 1!!  1!  1     !  *)
let mod3_1 f (a,b,c)  = (f a,b,c)
let mod3_3 f (a,b,c)  = (a,b,f c)
let mod4_1 f (a,b,c,d)  = (f a,b,c,d)
let mod4_4 f (a,b,c,d)  = (a,b,c,f d)
