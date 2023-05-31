functor Chialisp (S: CHIALISP_STRUCTS): CHIALISP =
struct

open S

(* Mirror compile.fun *)


structure Atoms = Atoms ()

local
  open Atoms
in
  structure Symbol = Symbol
  structure Con = Con
end

structure Ast = Ast (open Atoms)
structure FrontEnd = FrontEnd (structure Ast = Ast)

structure TypeEnv = TypeEnv (open Atoms)
structure Con = TypeEnv.Con
structure Tycon = TypeEnv.Tycon
structure CoreML = CoreML (open Atoms
                           structure Type =
                           struct
                           open TypeEnv.Type

                           val makeHom =
                            fn {con, var} =>
                               makeHom {con = con,
                                        expandOpaque = true,
                                        var = var}

                           fun layout t =
                               #1 (layoutPretty
                                       (t, {expandOpaque = true,
                                            layoutPrettyTycon = Tycon.layout,
                                            layoutPrettyTyvar = Tyvar.layout}))
                           end)
structure Elaborate = Elaborate (structure Ast = Ast
                                 structure CoreML = CoreML
                                 structure TypeEnv = TypeEnv)
structure Wrap = Region.Wrap

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
and CLBodyForm =
         CLLet of {kind: CLLetFormKind, bindings: CLBinding list, body: CLBodyForm}
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

fun selectKey (key: String.t) (j: JSON.value) =
    let
        fun findKey lst =
            case lst of
                [] => NONE
              | (k,v) :: tl =>
                if String.compare (k,key) = EQUAL then
                    SOME v
                else
                    findKey tl
    in
        case j of
            JSON.OBJECT l => findKey l
          | _ => NONE
    end

fun intArrayToString (j: JSON.value) =
    let
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
        optionMap ias (decodeListOf decodeInt j)
    end

fun fold_left f s l =
    let
        fun fl s l =
            case l of
                [] => s
              | hd :: tl =>
                let
                    val new_s = f s hd
                in
                    fl new_s tl
                end
    in
        fl s l
    end

fun intArrayToBigint (j: JSON.value) =
    let
        open List
        open String
        open IntInf

        val zero = IntInf.fromInt 0
        val eight_bits = IntInf.fromInt 256
        val per_digit = eight_bits * eight_bits * eight_bits * eight_bits

        fun combine a e = a * per_digit + e
    in
        optionMap
            (fold_left combine zero)
            (optionBind
                 (decodeListOf decodeInt)
                 (selectInArray 1 j)
            )
    end

fun decodeAtom (j: JSON.value) =
    optionMap
        (fn s => CLAtom s)
        (optionBind
             intArrayToString
             (selectInArray 1 j)
        )

fun decodeJSString (j: JSON.value) =
    case j of
        JSON.STRING s => SOME s
      | _ => NONE

fun decodeBool (j: JSON.value) =
    case j of
        JSON.BOOL b => SOME b
      | _ => NONE

fun decodeString (j: JSON.value) =
    optionMap
        (fn s => CLString s)
        (optionBind
             intArrayToString
             (selectInArray 2 j)
        )

fun decodeInteger (j: JSON.value) =
    optionMap
        (fn i => CLInteger i)
        (optionBind
             intArrayToBigint
             (selectInArray 1 j)
        )

fun decodeSExp (j: JSON.value) =
    let
        fun decodeSExp (j: JSON.value) =
            decodeJsonAlternatives j [
                ("Nil", fn _ => SOME CLNil),
                ("Atom", decodeAtom),
                ("QuotedString",decodeString),
                ("Integer", decodeInteger),
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

datatype DecodeBHC =
         DecodeBody of CLBodyForm option
       | DecodeHelper of CLHelperForm option
       | DecodeCompile of CLCompileForm option

fun decodeBHC (kind: DecodeBHC) (j: JSON.value): DecodeBHC =
    let
        fun decodeBinding j =
            let
                val name = optionBind intArrayToString (selectKey "name" j)
                val body = optionBind decodeBodyForm (selectKey "body" j)
            in
                case (name, body) of
                    (SOME name, SOME body) => SOME (CLBinding { name = name, body = body })
                  | _ => NONE
            end

        and decodeLetData (kind: String.t) j =
            let
                val bindings =
                    optionBind
                        (decodeListOf decodeBinding)
                        (selectKey "bindings" j)
                val body =
                    optionBind decodeBodyForm (selectKey "body" j)
                val ourKind =
                    if String.compare (kind, "Parallel") = EQUAL then
                        CLLFParallel
                    else
                        CLLFSequential
            in
                case (bindings, body) of
                    (SOME bindings, SOME body) => SOME (CLLet {kind = ourKind, bindings = bindings, body = body})
                  | _ => NONE
            end

        and decodeLetForm (j: JSON.value) =
            optionBind
                (fn kind =>
                    optionBind (decodeLetData kind) (selectInArray 1 j)
                )
                (optionBind decodeJSString (selectInArray 0 j))

        and decodeMod (j: JSON.value) =
            optionMap
                (fn m => CLMod m)
                (optionBind
                     decodeCompileForm
                     (selectInArray 0 j)
                )

        and decodeBodyForm (j: JSON.value) = decodeJsonAlternatives j [
            ("Value",
             fn j =>
                optionMap
                    (fn s => CLValue s)
                    (decodeSExp j)
            ),
            ("Quoted",
             fn j =>
                optionMap
                    (fn s => CLQuoted s)
                    (decodeSExp j)
            ),
            ("Call",
             fn j =>
                optionMap
                    (fn args => CLCall args)
                    (optionBind
                         (decodeListOf decodeBodyForm)
                         (selectInArray 1 j)
                    )
            ),
            ("Let", decodeLetForm),
            ("Mod", decodeMod)
            ]

        and decodeDefunData inline ddata =
            let
                val name = optionBind intArrayToString (selectKey "name" ddata)
                val args = optionBind decodeSExp (selectKey "args" ddata)
                val body = optionBind decodeBodyForm (selectKey "body" ddata)
            in
                case (name, args, body) of
                    (SOME name, SOME args, SOME body) =>
                    SOME (CLDefun {inline=inline, name=name, args=args, body=body})
                  | _ => NONE
            end

        and decodeDefun (j: JSON.value) =
            let
                val inline = optionBind decodeBool (selectInArray 0 j)
                val ddata = selectInArray 1 j
            in
                case (inline, ddata) of
                    (SOME inline, SOME ddata) => decodeDefunData inline ddata
                  | _ => NONE
            end

        and decodeMacro (j: JSON.value) =
            NONE

        and decodeConst (j: JSON.value) =
            NONE

        and decodeHelperForm (j: JSON.value) = decodeJsonAlternatives j [
            ("Defun", decodeDefun),
            ("Defmacro", decodeMacro),
            ("Defconst", decodeConst)
        ]

        and decodeCompileFormInner (args: JSON.value) (helpers: JSON.value) (exp: JSON.value): CLCompileForm option =
            let
                val decodedArgs = decodeSExp args
                val decodedHelpers = decodeListOf decodeHelperForm helpers
                val decodedExp = decodeBodyForm exp
            in
                case (decodedArgs, decodedHelpers, decodedExp) of
                    (SOME da, SOME dh, SOME de) => SOME (CLCompileForm { args = da, helpers = dh, body = de })
                  | _ => NONE
            end

        and decodeCompileForm (j: JSON.value): CLCompileForm option =
            case (selectKey "args" j, selectKey "helpers" j, selectKey "exp" j) of
                (SOME args, SOME helpers, SOME exp) =>
                decodeCompileFormInner args helpers exp
              | _ => NONE
    in
        case kind of
            DecodeBody _ => DecodeBody (decodeBodyForm j)
          | DecodeHelper _ => DecodeHelper (decodeHelperForm j)
          | DecodeCompile _ => DecodeCompile (decodeCompileForm j)
    end

fun decodeCompileForm (j: JSON.value) =
    case decodeBHC (DecodeCompile NONE) j of
        DecodeCompile c => c
      | _ => NONE

fun toSExpList (toSExp: 'a -> CLSExp) (l: 'a list) (tail: CLSExp) =
    let
        fun makeRest l =
            case l of
                [] => tail
              | hd :: tl =>
                let
                    val rest = makeRest tl
                in
                    CLCons {f = (toSExp hd), r = rest}
                end
    in
        makeRest l
    end

fun clformToSExp decodeBHC =
    let
        fun baseCompileFormToSExp args helpers body =
            let
                val expList = CLCons {f = bodyFormToSExp body, r = CLNil}
                val helperList = toSExpList helperFormToSExp helpers expList
            in
                CLCons
                    {
                      f = args,
                      r = helperList
                    }
            end

        and bindingToSExp (CLBinding {name:string, body:CLBodyForm}) =
            CLCons
                {
                  f = CLAtom name,
                  r =
                  CLCons
                      {
                        f = bodyFormToSExp body,
                        r = CLNil
                      }
                }

        and bodyFormToSExp b =
            case b of
                CLQuoted q =>
                CLCons
                    {
                      f = CLAtom "q",
                      r = q
                    }
              | CLValue (CLAtom a) => CLAtom a
              | CLValue v => bodyFormToSExp (CLQuoted v)
              | CLCall args => toSExpList bodyFormToSExp (reverse args) CLNil
              | CLMod (CLCompileForm {args:CLSExp,helpers:CLHelperForm list,body:CLBodyForm}) =>
                CLCons
                    {
                      f = CLAtom "mod",
                      r = baseCompileFormToSExp args helpers body
                    }
              | CLLet {kind:CLLetFormKind,bindings:CLBinding list,body:CLBodyForm} =>
                let
                    val kw =
                        case kind of
                            CLLFSequential => "let*"
                          | CLLFParallel => "let"

                    val bindings = toSExpList bindingToSExp bindings CLNil
                    val body = bodyFormToSExp body
                in
                    CLCons
                        {
                          f = CLAtom kw,
                          r =
                          CLCons
                              {
                                f = bindings,
                                r =
                                CLCons
                                    {
                                      f = body,
                                      r = CLNil
                                    }
                              }
                        }
                end

        and macroToSExp name margs (CLCompileForm { args:CLSExp, helpers:CLHelperForm list,body:CLBodyForm}) =
            CLCons
                {
                  f = CLAtom "defmacro",
                  r =
                  CLCons
                      {
                        f = CLAtom name,
                        r = baseCompileFormToSExp args helpers body
                      }
                }

        and helperFormToSExp h =
            case h of
                CLDefun {inline:bool,name:string,args:CLSExp,body:CLBodyForm} =>
                if inline then
                    CLCons
                        {
                          f = CLAtom "defun-inline",
                          r =
                          CLCons
                              {
                                f = CLAtom name,
                                r = baseCompileFormToSExp args [] body
                              }
                        }
                else
                    CLCons
                        {
                          f = CLAtom "defun",
                          r =
                          CLCons
                              {
                                f = CLAtom name,
                                r = baseCompileFormToSExp args [] body
                              }
                        }
              | CLDefmacro {name:string, args:CLSExp, body:CLCompileForm} =>
                macroToSExp name args body
              | CLDefconst {name:string, body:CLBodyForm} =>
                CLCons
                    {
                      f = CLAtom "defconstant",
                      r =
                      CLCons
                          {
                            f = CLAtom name,
                            r =
                            CLCons
                                {
                                  f = bodyFormToSExp body,
                                  r = CLNil
                                }
                          }
                    }

        and compileFormToSExpInner args helpers body =
            CLCons
                {
                  f = CLAtom "mod",
                  r = baseCompileFormToSExp args helpers body
                }

        and compileFormToSExp (CLCompileForm {args:CLSExp, helpers:CLHelperForm list, body:CLBodyForm}) =
            compileFormToSExpInner args helpers body
    in
        case decodeBHC of
            DecodeBody (SOME b) => bodyFormToSExp b
          | DecodeHelper (SOME h) => helperFormToSExp h
          | DecodeCompile (SOME c) => compileFormToSExp c
          | _ => CLNil
    end

fun compileFormToSExp cf = clformToSExp (DecodeCompile (SOME cf))

fun decodeFromJSON f (s: String.t) =
    let
        open JSON
    in
        f (JSONParser.parseFile s)
    end

fun toStrdec (dec: Ast.Dec.t): Ast.Strdec.t =
    let
        open Wrap
        open Ast

        val region: Region.t =
            Region.make {left=SourcePos.bogus, right=SourcePos.bogus}
    in
        Wrap.makeRegion (Strdec.Core dec, region)
    end

fun toStrdecs (decs: Ast.Strdec.t list): Ast.Strdec.t =
    let
        open Wrap
        open Ast

        val region: Region.t =
            Region.make {left=SourcePos.bogus, right=SourcePos.bogus}
    in
        Wrap.makeRegion (Strdec.Seq decs, region)
    end

fun toTopdec (dec: Ast.Strdec.t): Ast.Topdec.t =
    let
        open Wrap
        open Ast

        val region: Region.t =
            Region.make {left=SourcePos.bogus, right=SourcePos.bogus}
    in
        Wrap.makeRegion (Ast.Topdec.Strdec dec, region)
    end

fun programFromDecs (decs: Ast.Dec.t list): Ast.Program.t =
    let
        open Wrap
        open Ast

        val region: Region.t =
            Region.make {left=SourcePos.bogus, right=SourcePos.bogus}

        val strdecs: Ast.Strdec.t list = map toStrdec decs

        val topStrdec: Ast.Strdec.t = toStrdecs strdecs
    in
        Ast.Program.T [ [ toTopdec topStrdec ] ]
    end

val typeDeclForChialisp: Ast.Dec.t =
    let
        open Wrap
        open Ast
        open Atoms

        val region: Region.t =
            Region.make {left=SourcePos.bogus, right=SourcePos.bogus}

        (* Build the atom constructor *)
        val clAtomCon: Ast.Con.t =
            Ast.Con.fromSymbol (Symbol.fromString "CLAtom", region)

        val clConsCon: Ast.Con.t =
            Ast.Con.fromSymbol (Symbol.fromString "CLCons", region)

        val clTypeCon: Ast.Tycon.t =
            Ast.Tycon.fromSymbol (Symbol.fromString "CLSExp", region)

        val intInfLongtycon =
            Longtycon.fromSymbols
                ([Symbol.fromString "IntInf", Symbol.fromString "t"], region)

        val clTypeLongtycon =
            Longtycon.fromSymbols ([Symbol.fromString "CLSExp"], region)

        val intInfType =
            Wrap.makeRegion
                (Type.Con (intInfLongtycon, Vector.fromList []), region)

        val clType =
            Wrap.makeRegion
                (Type.Con (clTypeLongtycon, Vector.fromList []), region)

        val clSExpDatBind =
            Wrap.makeRegion (
                DatBind.T
                    {datatypes=
                     (Vector.fromList [{cons=
                                        (Vector.fromList [
                                              (clAtomCon, SOME intInfType),
                                              (clConsCon, SOME (Type.tuple (Vector.fromList [clType, clType])))
                                        ]),
                                        tycon=clTypeCon,
                                        tyvars=Vector.fromList []
                     }]),
                     withtypes=TypBind.empty
                    },
                region
            )

        val clDtRhs = Wrap.makeRegion (DatatypeRhs.DatBind clSExpDatBind, region)
    in
        Wrap.makeRegion (Dec.Datatype clDtRhs, region)
    end

fun chialispToML
        (CLCompileForm {
             args: CLSExp,
             helpers: CLHelperForm list,
             body: CLBodyForm
        }): Ast.Program.t =
    let
        open Wrap
        open Ast

        val region: Region.t =
            Region.make {left=SourcePos.bogus, right=SourcePos.bogus}

        fun convertExpression (exp: CLBodyForm): Ast.Exp.t =
            Wrap.makeRegion (Ast.Exp.Const (Wrap.makeRegion (Ast.Const.Int (IntInf.fromInt 0), region)), region)

        (* Functions in chialisp are unary
         * We write every function as:
         *
         * fun myfunc (arg: CLSExp): CLSExp = <body>
         *
         *)
        fun convertDefunDeclaration name args (body : CLBodyForm) =
            let
                val toplevelArgNames = Vector.fromList [
                        (Ast.Pat.var (Ast.Var.fromSymbol (Symbol.fromString name, region))),
                        (Ast.Pat.var (Ast.Var.fromSymbol (Symbol.fromString "arg", region)))
                    ]
                val letForm = convertExpression body
            in
                [Wrap.makeRegion (
                      (Ast.Dec.Fun
                           {tyvars=Vector.fromList [],
                            fbs=Vector.fromList [
                                Vector.fromList [
                                    {body=letForm,
                                     pats=toplevelArgNames,
                                     resultType=NONE
                                    }
                                ]
                           ]}
                      ), region
                  )]
            end

        fun convertDefconstDeclaration name (body: CLBodyForm) =
            let
                val constantName: Ast.Longvid.t =
                    Ast.Longvid.fromSymbols ([Symbol.fromString name], region)

                val pattern =
                    Wrap.makeRegion
                        (Ast.Pat.Var {fixop=Ast.Fixop.None, name=constantName},
                         region
                        )

                val convertedVbs = {exp=convertExpression body, pat=pattern}
            in
                [Wrap.makeRegion (
                      Ast.Dec.Val
                          {rvbs=Vector.fromList [],
                           tyvars=Vector.fromList [],
                           vbs=Vector.fromList [convertedVbs]
                          },
                      region
                  )
                ]
            end

        fun convertHelperDeclaration (decl: CLHelperForm): Ast.Dec.t list =
            case decl of
                CLDefun {inline, name, args, body} =>
                convertDefunDeclaration name args body
              | CLDefmacro dm => []
              | CLDefconst {name, body} => convertDefconstDeclaration name body

        val helperDeclarations: Ast.Dec.t list =
            List.concat (map convertHelperDeclaration helpers)

        val mainFunction: Ast.Dec.t list =
            []
    in
        programFromDecs
            (
              List.concat
                  [
                    [typeDeclForChialisp],
                    helperDeclarations,
                    mainFunction
                  ]
            )
    end

fun frontendChialispToCoreDecs (fe: Ast.Program.t): Elaborate.Env.Decs.t =
    let
        open Elaborate
    in
        Programs.elaborateProgram (fe, {env=Env.empty ()})
    end

fun readSsaJson (fname: String.t) =
    let
        val decodedProgram = decodeFromJSON decodeCompileForm fname

        val prog =
            case decodedProgram of
                SOME p => SOME (chialispToML p)
              | NONE => NONE
    in
        case prog of
            SOME s =>
            let
                val progLayout = Ast.Program.layout s
            in
                print (Layout.toString progLayout)
            end
          | NONE => print "didn't convert"
    end
end
