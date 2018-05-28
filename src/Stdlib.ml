(* Module for functions that should be in prelude, but for some reason they are not *)

open List

let flip x a b = x b a
let id x = x
let foldl = fold_left
let foldr = fold_right
let swap (a,b) = (b,a)
let const x = fun _ -> x
(* Composition... *)
let (%) a b = fun x -> a (b x)

(* that's a parody of bifunctors, right *)
let second f (a,b) = (a,f b)
let first f (a,b) = (f a,b)

(* fromMaybe *)
let fromSome = function | Some x -> x | None -> failwith "fromRes: failed to resolve None"

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
