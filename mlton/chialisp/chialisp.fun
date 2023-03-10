functor Chialisp (S: CHIALISP_STRUCTS): CHIALISP =
struct

open S

(* Mirror of chialisp HelperForm and BodyForm *)
datatype CLSExp =
   CLNil
 | CLInteger of IntInf.t
 | CLHexConstant of String.t
 | CLString of String.t
 | CLAtom of String.t
 | CLCons of {f: CLSExp, r: CLSExp}

datatype CLLetFormKind = CLLFSequential
                       | CLLFParallel

and CLBinding = CLBinding of { name: String.t, body: CLBodyForm }
and CLLetData = CLLetData of { bindings: CLBinding list }

and CLBodyForm =
         CLLet of {kind: CLLetFormKind, data: CLLetData}
       | CLQuoted of CLSExp
       | CLValue of CLSExp
       | CLCall of CLBodyForm list
       | CLMod of CLCompileForm
and CLHelperForm =
         CLDefun of {inline: bool, name: String.t, args: CLSExp, body: CLBodyForm}
       | CLDefmacro of {name: String.t, args: CLSExp, body: CLCompileForm }
       | CLDefconst of {name: String.t, body: CLBodyForm}
and CLCompileForm = CLCompileForm of {
             args: CLSExp,
             helpers: CLHelperForm list,
             body: CLBodyForm
         }

fun filter (f : 'a -> bool) (lst : 'a list) =
    let
        fun filter_inner lst =
            case lst of
                [] => []
              | hd :: tl => if f hd then hd :: filter_inner tl else filter_inner tl
    in
        filter_inner lst
    end

fun ifMatchJsonAlternative (j: JSON.value) (name: String.t) (f: JSON.value -> 'a option) =
    let
        fun nameMatches (n,v): bool = String.compare (n,name) = EQUAL

        val matches =
            case j of
                JSON.OBJECT pairs => filter nameMatches pairs
              | x => []
    in
        case matches of
            [] => NONE
          | (_,v) :: _ => f v
    end

fun filterMap (f: 'a -> 'b option) (lst: 'a list) =
    let
        fun filterMap_inner lst =
            case lst of
                [] => []
              | hd :: tl =>
                case f hd of
                    NONE => filterMap_inner tl
                  | SOME x => x :: (filterMap_inner tl)
    in
        filterMap_inner lst
    end

fun decodeJsonAlternatives (j: JSON.value) (fns: (string * (JSON.value -> 'a option)) list) =
    let
        val matches =
            filterMap (fn (n,f) => ifMatchJsonAlternative j n f) fns
    in
        case matches of
           [] => NONE
         | hd :: tl => SOME hd
    end

fun optionMap (f: 'a -> 'b) (oval: 'a option) =
    case oval of
        NONE => NONE
      | SOME v => SOME (f v)

fun optionBind (f: 'a -> 'b option) (oval: 'a option) =
    case oval of
        NONE => NONE
      | SOME v => f v

fun foldLeft (f: 'b -> 'a -> 'b) (init: 'b) (lst: 'a list) =
    let
        fun iterateList init lst =
            case lst of
                [] => init
              | hd :: tl => iterateList (f init hd) tl
    in
        iterateList init lst
    end

fun sexpToDebugString (sexp: CLSExp) =
    let
        open IntInf

        fun rest fi re =
            case re of
                CLNil => (main fi) ^ ")"
              | CLCons {f, r} => (main fi) ^ " " ^ (rest f r)
              | _ => (main fi) ^ " . " ^ (main re) ^ ")"

        and main sexp =
            case sexp of
                CLNil => "()"
              | CLAtom s => "[" ^ s ^ "]"
              | CLCons {f, r} => "(" ^ rest f r
              | CLInteger i => IntInf.toString i
              | CLString s => "\"" ^ s ^ "\""
              | CLHexConstant s => s
    in
        main sexp
    end

fun debugOutputJSON (j: JSON.value) =
    let
        val _ = JSONPrinter.print (Pervasive.TextIO.stdOut, j)
    in
        j
    end

fun reverse (lst: 'a list) =
    let
        val l = ref []
        fun revList lst =
            case lst of
                [] => ()
              | hd :: tl =>
                (l := hd :: (!l) ; revList tl)
    in
        revList lst ; !l
    end

fun decodeInt (j: JSON.value) =
    case j of
       JSON.INT i => SOME i
     | _ => NONE

fun decodeListOf (f: JSON.value -> 'a option) (j: JSON.value) =
    let
        fun folder init elt =
            optionBind
                (fn init =>
                    optionMap (fn res => (res :: init)) (f elt)
                )
                init

        fun decodeList lst =
            foldLeft
                folder
                (SOME [])
                lst
    in
        case j of
            JSON.ARRAY vs => decodeList vs
          | _ => NONE
    end

fun selectInArray (n: int) (j: JSON.value) =
    let
        fun findN n lst =
            case lst of
               [] => NONE
             | hd :: tl =>
               if n < 1 then
                   SOME hd
               else
                   findN (n - 1) tl
    in
        case j of
            JSON.ARRAY vs => findN n vs
          | _ => NONE
    end

fun intArrayToString (j: JSON.value) =
    let
        val _ = print "intArrayToString"
        fun ias is =
            let
                open List
                open String
                open IntInf

                val mapped =
                    List.map (is, (fn i => Char.toString (Char.chr (IntInf.toInt i))))
            in
                String.concat (reverse mapped)
            end
    in
        optionMap ias (decodeListOf decodeInt (debugOutputJSON j))
    end

fun decodeAtom (j: JSON.value) =
    let
        val _ = print "decodeAtom"
    in
        optionMap
            (fn s => CLAtom s)
            (optionBind
                 intArrayToString
                 (selectInArray 1 (debugOutputJSON j))
            )
    end

fun decodeSExp (j: JSON.value) =
    let
        fun decodeSExp (j: JSON.value) =
            decodeJsonAlternatives j [
                ("Nil", fn _ => SOME CLNil),
                ("Atom", decodeAtom),
                ("Cons", decodeCons)
            ]

        and decodeCons (j: JSON.value) =
            let
                val firstElt = optionBind decodeSExp (selectInArray 1 j)

                val secondElt = optionBind decodeSExp (selectInArray 2 j)
            in
                optionBind
                    (fn first =>
                        optionMap
                            (fn snd => CLCons {f = first, r = snd})
                            secondElt
                    )
                    firstElt
            end
    in
        decodeSExp j
    end

fun decodeSExpFromJSON (s: String.t) =
    let
        open JSON
    in
        decodeSExp (JSONParser.parseFile s)
    end

fun readSsaJson (fname: String.t) =
    case decodeSExpFromJSON fname of
        SOME s => print (sexpToDebugString s)
      | NONE => print "didn't decode"

end
