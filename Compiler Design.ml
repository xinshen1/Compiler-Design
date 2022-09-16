type const = Unit | Int of int | Bool of bool | Name of string

type com = Push of const| Pop of int | Trace of int | Add of int | Sub of int| Mul of int | Div of int | And | Or  | Not| Equal | Lte | Local | Global | Lookup | Begin of ((com list)) | If of ( (com list)* (com list)) | Call | Fun of string * string * coms | Try of coms | Switch of (const * com list) list

and coms = com list

and env = (string * value) list

and value = VUnit | VInt of int | VBool of bool | VName of string | Clo of (env * string * string * coms)

type stack = value list

type log = string list


(* parsing util functions *)

let is_lower_case c = 'a' <= c && c <= 'z'

let is_upper_case c = 'A' <= c && c <= 'Z'

let is_alpha c = is_lower_case c || is_upper_case c

let is_digit c = '0' <= c && c <= '9'

let is_alphanum c = is_lower_case c || is_upper_case c || is_digit c

let is_blank c = String.contains " \012\n\r\t" c

let explode s = List.of_seq (String.to_seq s)

let implode ls = String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ loop ()
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option = p (explode s)

let pure (x : 'a) : 'a parser = fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

let ( >>= ) = bind

let ( let* ) = bind

let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then
      Some (x, ls)
    else
      None
  | _ -> None

let char (c : char) : char parser = satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let ( >> ) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) -> (
      match p2 ls with
      | Some (_, ls) -> Some (x, ls)
      | None -> None)
  | None -> None

let ( << ) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) -> Some (x, ls)
  | None -> p2 ls

let ( <|> ) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let ( >|= ) = map

let ( >| ) p c = map p (fun _ -> c)

let rec many (p : 'a parser) : 'a list parser =
  fun ls ->
  match p ls with
  | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : 'a list parser =
  fun ls ->
  match p ls with
  | Some (x, ls) -> (
      match many p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : 'a list parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : 'a list parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) -> (
      match many' p ls with
      | Some (xs, ls) -> Some (x :: xs, ls)
      | None -> Some ([ x ], ls))
  | None -> None

let whitespace : unit parser =
  fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c then
      Some ((), ls)
    else
      None
  | _ -> None

let ws : unit parser = many whitespace >| ()

let ws1 : unit parser = many1 whitespace >| ()

let digit : char parser = satisfy is_digit

let natural : int parser =
  fun ls ->
  match many1 digit ls with
  | Some (xs, ls) -> Some (int_of_string (implode xs), ls)
  | _ -> None





let literal (s : string) : unit parser =
  fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match (cs, ls) with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c then
        loop cs xs
      else
        None
    | _ -> None
  in
  loop cs ls

let keyword (s : string) : unit parser = literal s >> ws >| ()

let string_of x =
  match x with 
    VUnit -> "()"
  |
    VInt a -> string_of_int a
  |
    VBool a -> if a == true then "True"
    else 
      "False"
  |
    VName a -> a
  |
    Clo (env, x1, x2, cmds) -> x1


let reserved = [
  "push";
  "pop";
  "True";
  "False";
  "Add";
  "Sub";
  "Mul";
  "Div";
  "And";
  "Or";
  "Equal";
  "Lte";
  "Local";
  "Global";
  "Lookup";
  "Begin";
  "End";
  "If";
  "Else"
]

let int_parser () =
  (let* n = natural in
   pure (Int n) << ws)
  <|> let* _ = keyword "-" in
  let* n = natural in
  pure (Int (-n)) << ws

let rec pushCommand () =
  satisfy (fun x->x = 'P') >>= fun _->
  satisfy (fun x->x = 'u') >>= fun _->
  satisfy (fun x->x = 's') >>= fun _->
  satisfy (fun x->x = 'h') >>= fun _->
  whitespace >>= fun i->
  (
    natural >>= fun i->
    pure (Push (Int i)) << ws
  )
  <|>
  (
    satisfy (fun x->x = '(') >>= fun _->
    satisfy (fun x->x = ')') >>= fun _->
    pure (Push Unit) << ws
  )
  <|>
  (
    satisfy (fun x->x = 'T') >>= fun _->
    satisfy (fun x->x = 'r') >>= fun _->
    satisfy (fun x->x = 'u') >>= fun _->
    satisfy (fun x->x = 'e') >>= fun _->
    pure (Push (Bool true)) << ws
  )
  <|>
  (
    satisfy (fun x->x = 'F') >>= fun _->
    satisfy (fun x->x = 'a') >>= fun _->
    satisfy (fun x->x = 'l') >>= fun _->
    satisfy (fun x->x = 's') >>= fun _->
    satisfy (fun x->x = 'e') >>= fun _->
    pure (Push (Bool false)) << ws
  )
  <|> 
  (
    let* c = satisfy (is_alpha ) in 
    let* cs = many  (satisfy (fun a -> (is_alphanum a) || a =  '_' || a=  '\'' || a=  '?') ) in
    let s = implode (c::cs) in 
    if List.exists (fun x -> x = s) reserved then fail
    else
      pure (Push (Name s)) << ws
  )

let st =  let* c = satisfy (is_alpha ) in 
  let* cs = many  (satisfy (fun a -> (is_alphanum a) || a =  '_' || a=  '\'' || a=  '?') ) in
  let s = implode (c::cs) in 
  if List.exists (fun x -> x = s) reserved then fail
  else
    pure (s) << ws

let rec popCommand () =
  satisfy (fun x->x = 'P') >>= fun _->
  satisfy (fun x->x = 'o') >>= fun _->
  satisfy (fun x->x = 'p') >>= fun _->
  whitespace >>= fun i->
  natural >>= fun i->
  pure (Pop i)  << ws

let rec traceCommand () =
  satisfy (fun x->x = 'T') >>= fun _->
  satisfy (fun x->x = 'r') >>= fun _->
  satisfy (fun x->x = 'a') >>= fun _->
  satisfy (fun x->x = 'c') >>= fun _->
  satisfy (fun x->x = 'e') >>= fun _->
  whitespace >>= fun i->
  natural >>= fun i->
  pure (Trace i)   << ws

let rec addCommand () =
  satisfy (fun x->x = 'A') >>= fun _->
  satisfy (fun x->x = 'd') >>= fun _->
  satisfy (fun x->x = 'd') >>= fun _->
  whitespace >>= fun i->
  natural >>= fun i->
  pure (Add i)  << ws

let rec subCommand () =
  satisfy (fun x->x = 'S') >>= fun _->
  satisfy (fun x->x = 'u') >>= fun _->
  satisfy (fun x->x = 'b') >>= fun _->
  whitespace >>= fun i->
  natural >>= fun i->
  pure (Sub i)  << ws

let rec mulCommand () =
  satisfy (fun x->x = 'M') >>= fun _->
  satisfy (fun x->x = 'u') >>= fun _->
  satisfy (fun x->x = 'l') >>= fun _->
  whitespace >>= fun i->
  natural >>= fun i->
  pure (Mul i)  << ws

let rec divCommand () =
  satisfy (fun x->x = 'D') >>= fun _->
  satisfy (fun x->x = 'i') >>= fun _->
  satisfy (fun x->x = 'v') >>= fun _->
  whitespace >>= fun i->
  natural >>= fun i->
  pure (Div i)  << ws

let rec andCommand () =
  satisfy (fun x->x = 'A') >>= fun _->
  satisfy (fun x->x = 'n') >>= fun _->
  satisfy (fun x->x = 'd') >>= fun _->
  pure (And)  << ws

let rec orCommand () =
  satisfy (fun x->x = 'O') >>= fun _->
  satisfy (fun x->x = 'r') >>= fun _->
  pure (Or)  << ws

let rec notCommand () =
  satisfy (fun x->x = 'N') >>= fun _->
  satisfy (fun x->x = 'o') >>= fun _->
  satisfy (fun x->x = 't') >>= fun _->
  pure (Not)  << ws

let rec equalCommand () =
  satisfy (fun x->x = 'E') >>= fun _->
  satisfy (fun x->x = 'q') >>= fun _->
  satisfy (fun x->x = 'u') >>= fun _->
  satisfy (fun x->x = 'a') >>= fun _->
  satisfy (fun x->x = 'l') >>= fun _->
  pure (Equal)  << ws

let rec lteCommand () =
  satisfy (fun x->x = 'L') >>= fun _->
  satisfy (fun x->x = 't') >>= fun _->
  satisfy (fun x->x = 'e') >>= fun _->
  pure (Lte)  << ws

let rec localCommand ()  =
  keyword ("Local") >>= fun _->
  pure (Local)  << ws

let rec globalCommand ()  =
  keyword ("Global") >>= fun _->
  pure (Global)  << ws

let rec lookupCommand () =
  keyword ("Lookup") >>= fun _->
  pure (Lookup)  << ws

let comm ()=
  pushCommand () <|> popCommand () <|> traceCommand () <|> addCommand () <|> subCommand () <|> mulCommand () <|> divCommand () <|> andCommand () <|> orCommand () <|> notCommand () <|> equalCommand () <|> lteCommand ()
  <|> localCommand () <|> globalCommand () <|> lookupCommand ()



let rec beginCommand () =
  keyword ("Begin") >>= fun _ -> 
  many((commandParser ())) >>= fun x ->
  keyword ("End") >>= fun _ ->
  pure (Begin(x)) << ws


and ifCommand () =
  keyword ("If") >>= fun _ -> 
  many((commandParser ())) >>= fun x ->
  keyword ("Else") >>= fun _ ->
  many((commandParser ())) >>= fun y ->
  keyword ("End") >>= fun _ ->
  pure (If(x,y)) << ws

and funCommand () =
  let* _ = keyword "Fun" in
  let* funName = st in
  let* v = st in
  let* c = many (commandParser ()) in
  let* _ = keyword "End" in
  pure (Fun (funName, v, c)) << ws

and callCommand () =
  let* _ = keyword "Call" in
  pure Call << ws

and tryCommand () =
  let* _ = keyword "Try" in
  let* c =  many (commandParser ()) in
  let* _ = keyword "End" in
  pure (Try c) << ws


and switchCommand () =
  let* a = keyword "Switch" in
  let* case = many (
      let* b = keyword "Case" in
      let* i = int_parser () in
      let* c = many (commandParser ()) in
      pure (i, c)
    ) in
  let* d = keyword "End" in
  pure (Switch case) << ws


and commandParser  () = 
  comm ()<|> beginCommand ()  <|> ifCommand () <|> funCommand () <|> callCommand () <|> tryCommand () <|> switchCommand ()




(* end of parser combinators *)
let rec popn (a: int) s =
  if a < 0 then None
  else
  if a = 0 then Some s
  else
    match s with
      [] -> if a > 0 then None
      else
        Some []
    |
      h::t -> if a > 1 then popn (a-1) t
      else
        Some t

let rec tracen (a: int) s  = 
  if a < 0 then None
  else
  if a = 0 then Some ([],s)
  else 
    match s with
      [] ->  None
    |
      h::t ->  
      (
        match tracen (a-1) t with
          None -> None
        |
          Some (log,t) ->  Some ( string_of h :: log,t)

      )



let rec addn (a:int) s =
  if a<0 then None
  else 
  if a = 0 then Some (VInt 0::s)
  else
    let rec aux a s sum =
      match s with
        [] -> if a>0 then None
        else Some(VInt sum :: s)
      |
        h::t -> if a>0 then 
          (match h with
             VInt b -> aux (a-1) t (b+sum)
           |
             _-> None
          )
        else Some(VInt sum ::s)
    in aux a s 0 



let rec subn (a:int) s =
  if a<0 then None
  else
  if a=0 then Some (VInt 0::s)
  else
    match s with
      (VInt x) :: y -> 
      (
        let rec aux a s1 di =
          if a = 0 then Some (VInt di :: s1)
          else
            match s1 with
              [] -> None
            |
              VInt b :: rem -> aux (a-1) rem (di-b)
            |
              _-> None
        in aux (a-1) y x
      )
    |
      _-> None


let rec muln (a:int) s =
  if a<0 then None
  else 
  if a = 0 then Some (VInt 1::s)
  else
    let rec aux a s mu =
      match s with
        [] -> if a>0 then None
        else Some(VInt mu :: s)
      |
        h::t -> if a>0 then 
          (match h with
             VInt b -> aux (a-1) t (b * mu)
           |
             _-> None
          )
        else Some(VInt mu ::s)
    in aux a s 1 

let rec divn (a:int) s =
  if a<0 then None
  else 
  if a = 0 then Some (VInt 1::s)
  else
    match s with
      (VInt a1):: b1 -> 
      (
        let rec aux a s di =
          match s with
            [] -> if a>0 then None
            else Some(VInt di :: s)
          |
            h::t -> if a>0 then 
              (match h with
                 VInt b -> if b == 0 then None
                 else
                   aux (a-1) t (di/b)
               |
                 _-> None
              )
            else Some(VInt di ::s)
        in aux (a-1) b1 a1 
      )
    |
      _-> None


let rec andb s =
  match s with
    VBool a1:: VBool a2:: rem -> Some (VBool (a1 && a2) :: rem)
  |
    _ -> None


let rec orb s =
  match s with
    VBool a1:: VBool a2:: rem -> Some (VBool (a1 || a2) :: rem)
  |
    _ -> None

let rec notb s =
  match s with
    VBool a1:: rem -> Some (VBool (not a1) :: rem)
  |
    _ -> None

let rec equalb s =
  match s with
    VInt a1 :: VInt a2 :: rem -> Some (VBool (a1=a2) :: rem)
  |
    _ -> None

let rec lteb s =
  match s with
    VInt a1 :: VInt a2 :: rem -> Some (VBool (a1<=a2) :: rem)
  |
    _ -> None


let rec lookup (global: env) (local: env) a  =

  match lookupl local a with
    None -> 
    (
      match lookupg global a with
        None -> None
      |
        Some result -> Some result
    )
  |
    Some result -> Some result


and lookupl local a =
  match local with
    (s, x2) :: rem -> if s = a then Some x2 
    else
      lookupl rem a
  |
    _-> None

and lookupg global a = 
  match global with
    (s, x2) :: rem -> if s = a then Some x2 
    else
      lookupg rem a
  |
    _-> None

let rec call (global: env) (local: env) s =
  match s with 
    Clo (l, name, v, c ) :: t ->
    (
      match t with
        [] -> None
      |
        hd :: ti -> Some( (name, Clo ((l,name,v,c)))::(v,hd)::l, ti, c)
    )
  |
    _ -> None

let rec switch case n =
  match case with
    [] -> None
  |
    (Int i,c) :: ta -> if i == n then Some c
    else switch ta n
  |
    (_, c) :: t -> None
(**
   e1 ---- global
   e2 ---- local
*)
let rec run (l: log) (e1: env) (e2: env) (s: stack) (c: coms) : (env *log * stack option) =
  match c with
    [] -> (e1, l, Some s)
  |
    (Push x)::t -> 
    (
      match x with 
        Unit -> run l e1 e2 (VUnit::s) t
      |
        Int i -> run l e1 e2 (VInt i ::s) t
      |
        Bool i -> run l e1 e2 (VBool i ::s) t
      |
        Name i -> run l e1 e2 (VName i ::s) t
    )
  | 
    (Pop x)::t -> 
    (
      match popn x s with 
        None ->  (e1, l, None)
      |
        Some r -> run l e1 e2 r t
    )
  |
    (Trace x)::t -> 
    (
      match tracen x s  with 
        None -> (e1, l, None)
      |
        Some (l1,r) -> run ( List.rev l1 @ l) e1 e2 r t
    )

  |
    (Add x)::t ->
    (
      match addn x s with 
        None -> (e1, l, None)
      |
        Some s ->  run l e1 e2 s t
    )

  |
    (Sub x)::t -> 
    (
      match subn x s with 
        None -> (e1, l, None)
      |
        Some s ->  run l e1 e2 s t
    )
  |
    (Mul x)::t ->  
    (
      match muln x s with 
        None -> (e1, l, None)
      |
        Some s ->  run l e1 e2 s t
    )

  |
    (Div x)::t -> 
    (
      match divn x s with 
        None -> (e1, l, None)
      |
        Some s ->  run l e1 e2 s t
    )
  |
    (And) :: t -> 
    (
      match andb s with
        None -> (e1, l, None)
      |
        Some s -> run l e1 e2 s t
    )
  |
    (Or) :: t -> 
    (
      match orb s with
        None -> (e1,l, None)
      |
        Some s -> run l e1 e2 s t
    )
  |
    (Not) :: t -> 
    (
      match notb s with
        None -> (e1, l, None)
      |
        Some s -> run l e1 e2 s t
    )
  |
    (Equal) :: t -> 
    (
      match equalb s with
        None -> (e1, l, None)
      |
        Some s -> run l e1 e2 s t
    )
  |
    (Lte) :: t -> 
    (
      match lteb s with
        None -> (e1, l, None)
      |
        Some s -> run l e1 e2 s t
    )
  |
    (Local) :: t -> 
    (
      match s with
        VName x :: y :: z  -> run l e1 ((x,y)::e2) (VUnit::z) t
      |
        _ -> (e1, l, None)
    )
  |
    (Global) :: t -> 
    (
      match s with
        VName x :: y :: z  -> run l ((x,y)::e1) e2 (VUnit::z) t
      |
        _ -> (e1, l, None)
    )
  |
    (Lookup) :: t -> 
    (
      match s with
        VName a :: rem ->(
          match lookup e1 e2 a with
            Some x -> run l e1 e2 (x :: rem) t
          |
            None -> (e1, l, None)
        )
      |
        _ -> (e1, l, None)
    )
  |
    (Begin x) :: t -> 
    ( 
      match run l e1 e2  [] x with
        (e1, l1, Some (hd::ta)) -> run l1 e1 e2 (hd :: s) t
      |
        _-> (e1, l, None)
    )
  |
    (If (x,y)) :: t ->
    (
      match s with
        (VBool true):: rem -> run l e1 e2 rem (x @ t)
      |
        (VBool false):: rem -> run l e1 e2 rem (y @ t)
      |
        _ -> (e1, l, None)
    )
  |
    (Fun (name, v, c)):: t -> run l e1 ((name, Clo(e2,name,v,c))::e2) s t
  |
    Call :: t-> 
    (
      match call e1 e2 s with 
        None -> (e1, l, None)
      |
        Some (new_local, r, c1) -> (
          match run l e1 new_local [] c1 with

            (_,l1,Some (a :: b)) -> run l e1 e2 (a :: r) t
          |
            _ -> (e1, l, None)
        )
    )
  | 
    Try c :: t -> 
    (
      match run l e1 e2 [] c with
        (g, l1,  a) -> match a with
          Some (h :: ta) -> run l1 g e2 (h :: s) t
        |
          _ -> run l e1 e2 s t

    )
  |
    Switch c :: t -> 
    (
      match s with
        VInt i :: tail ->( match switch c i with
            Some com -> run l e1 e2  tail (com @ t)
          |
            _-> (e1, l, None)
        )
      |
        _ -> (e1, l, None)
    )




(* TODO *)
let interp (src : string) : string list = 
  match ( parse (ws >> many (commandParser ())) src) with 
    Some (c, []) -> 
    (
      match run [] [] [] [] c with
        (_,l,Some _) -> l
      |

        (_, _, None) -> ["Error"]
    )
  |
    _ -> ["Error"]




(* Calling (main "test.txt") will read the file test.txt and run interp on it.
   This is only used for debugging and will not be used by the gradescope autograder. *)
let main fname =
  let src = readlines fname in
  interp src