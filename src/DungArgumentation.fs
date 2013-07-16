#if INTERACTIVE
#r "packages/NUnit.2.6.2/lib/nunit.framework.dll"
#else
// This module implements Dung's argumentation frameworks.
module SharpLogic.Dung
#endif

// (
//    -- * Basic definitions 
//   DungAF(..),
//   setAttacks, conflictFree, acceptable, f, admissible, unattacked, attacked,
//   -- * Grounded semantics through fixpoints and labelling
//   fixpoint, Status(..), grounded, groundedExt)
// where
//import Data.List (intersect, (\\))

open System

/// An abstract argumentation framework is a set of arguments
/// (represented as a list) and an attack relation on these arguments.
type DungAF<'a>   = AF of Arguments<'a> * Attacks<'a>
and Arguments<'a> = 'a list
and Attacks<'a>   = ('a * 'a) list

module List =
  /// returns True if the list contains any True element
  let ``or`` = List.fold (fun acc t -> acc || t) false
  let ``null`` = List.isEmpty
  let ``and`` = List.fold (fun acc t -> acc && t) true
  ///  returns True if the list contains an item equal to the first argument
  let elem (l : 'a list) (i : 'a) = l |> List.map (fun t -> t = i) |> ``or``
  /// Alias for filter, keep all items in the list where the predicate returns true
  let keep = List.filter
  /// cut ys from xs, i.e. remove all x items from xs whenever x is in ys
  let cut xs ys = xs |> keep (fun x -> not <| elem ys x)

open NUnit.Framework

let [<Test>] ``List.or``() = [ true; false; true ] |> List.``or`` |> Assert.IsTrue
let [<Test>] ``List.or'`` () = [ false ] |> List.``or`` |> Assert.IsFalse
let [<Test>] ``List.or''`` () = [ true ] |> List.``or`` |> Assert.IsTrue
let [<Test>] ``List.or'''`` () = [] |> List.``or`` |> Assert.IsFalse

let [<Test>] ``List.null``() = [] |> List.``null`` |> Assert.IsTrue
let [<Test>] ``List.null'``() = [ 'a' ] |> List.``null`` |> Assert.IsFalse

let [<Test>] ``List.and``() = [ true; false ] |> List.``and`` |> Assert.IsFalse
let [<Test>] ``List.and'``() = [ true; true ] |> List.``and`` |> Assert.IsTrue
let [<Test>] ``List.and''``() = [] |> List.``and`` |> Assert.IsTrue

let [<Test>] ``List.elem`` () = 'a' |> List.elem [ 'a' ] |> Assert.IsTrue
let [<Test>] ``List.elem'`` () = 'b' |> List.elem [ 'a' ] |> Assert.IsFalse
let [<Test>] ``List.elem''`` () = 'c' |> List.elem [] |> Assert.IsFalse

let [<Test>] ``List.cut`` () = [ 'a' ] |> List.cut [ 'a' ] |> (fun l -> Assert.AreEqual([], l))
let [<Test>] ``List.cut'`` () = [ 'a' ] |> List.cut [ 'b' ] |> (fun l -> Assert.AreEqual( ['b'], l))
let [<Test>] ``List.cut''`` () = [ 'b' ] |> List.cut [ 'a' ] |> (fun l -> Assert.AreEqual( ['a'], l))

/// Given an argumentation framework, determines whether args
/// (subset of the arguments in the AF), attacks an argument arg (in the AF).
/// setAttacks :: Eq arg => DungAF arg -> [arg] -> arg -> Bool
let setAttacks (af : DungAF<_>) (args : 'a list) (arg : 'a) =
  // or [b == arg | (a, b) <- def, a `elem` args] 
  let (AF (_, def)) = af
  [ for (_, b) in def |> List.filter (fst >> (List.elem args))
      do yield b = arg ]
  |> List.``or``

let [<Test>] ``AF contains counterargument, then set attacks`` () =
  setAttacks (AF(["a"; "b"], [("b", "a"); ("b", "c")])) ["b"] "a"
  |> Assert.IsTrue

let [<Test>] ``AF does not contain counterargument, then set does not attack`` () =
  setAttacks (AF(["a"; "b"], [("b", "a"); ("b", "c")])) ["c"] "a"
  |> Assert.IsFalse

/// Given an argumentation framework, determines whether args
/// (subset of the arguments in the AF) is conflict-free.
/// conflictFree :: Eq arg => DungAF arg -> [arg] -> Bool
let conflictFree af args =
  // null [(a,b) | (a, b) <- def, a `elem` args, b `elem` args]
  let inargs = List.elem args
  let (AF (_, def)) = af
  [ for a, b in def do if inargs a && inargs b then yield a, b ]
  |> List.``null``

let [<Test>] ``arguments given are conflict free if set of attack pairs doesn't contain them`` () =
  // second parameter being tested
  conflictFree (AF (["a"], [])) ["a"] |> Assert.IsTrue
  conflictFree (AF (["a"; "b"], [])) ["a"] |> Assert.IsTrue
  conflictFree (AF (["a"; "b"], [("a", "b")])) ["a"] |> Assert.IsTrue

let [<Test>] ``arguments given are not conflict free`` () =
  conflictFree (AF (["a"; "b"], [("a", "b")])) ["a"; "b"] |> Assert.IsFalse
  conflictFree (AF (["a"; "b"], [("b", "a")])) ["a"; "b"] |> Assert.IsFalse

let internal shouldLearn =
  AF (["is_fun"; "is_hard"; "feeling_of_accomplishment"], 
      [("is_hard", "is_fun"); ("feeling_of_accomplishment", "is_hard")])

/// Given an argumentation framework, determines whether an 
/// argument is acceptable with respect to a list of 'args'
/// (subset of the arguments in the AF).
/// I.e. whenever an argument
/// in the argumentation framework attacks 'a', there exists another
/// argument in the argumentation framework that attacks that argument.
/// acceptable :: Eq arg => DungAF arg -> arg -> [arg] -> Bool
let acceptable af a args =
  // and [setAttacks af args b | (b, a') <- def, a == a']
  let (AF (_, def)) = af
  [ for (b, a') in def do if a = a' then yield setAttacks af args b ]
  |> List.``and``


let [<Test>] ``argument: 'is fun' is acceptable given a 'feeling_of_accomplishment'`` () =
  acceptable shouldLearn "is_fun" ["is_fun"; "feeling_of_accomplishment"]
  |> Assert.IsTrue

let [<Test>] ``argument: 'is fun' is acceptable given only the counter argument`` () =
  acceptable shouldLearn "is_fun" ["is_fun"; "is_hard"]
  |> Assert.IsFalse

/// Given an argumentation framework, determines whether all
/// arguments from the framework are acceptable with respect to 'args'.
/// (subset of the arguments in the AF).
/// f :: Eq arg => DungAF arg -> [arg] -> [arg]
let acceptableFwArgs af args = 
  //[a | a <- args', acceptable af a args]
  let (AF (args', _)) = af
  args' |> List.filter (fun a -> acceptable af a args)

let [<Test>] ``fw shouldStudy is acceptable with respect to all arguments in it`` () =
  let (AF (args, _)) = shouldLearn
  acceptableFwArgs shouldLearn args
  |> fun l -> CollectionAssert.AreEquivalent(["is_fun"; "feeling_of_accomplishment"], l)

/// Returns 'True' if 'xs' is a subset of 'ys'
/// subset :: Eq a => [a] -> [a] -> Bool
let subset xs ys =
  // xs `subset` ys = null (xs \\ ys)
  List.``null`` (List.cut xs ys)

let [<Test>] ``[a] is subset of [a,b]`` () =
  subset ['a'] ['a'; 'b'] |> Assert.IsTrue
let [<Test>] ``[a] is subset of [a]`` () =
  subset ['a'] ['a'] |> Assert.IsTrue
let [<Test>] ``[a] is not subset of [b]`` () =
  subset ['a'] ['b'] |> Assert.IsFalse

/// Given an argumentation framework, determines whether
/// the set of arguments 'args' (subset of the arguments in the AF) is admissible,
/// i.e. if 'args' is 'conflictFree' and args is a subset of @acceptableFwArgs af args@
/// admissible :: Eq arg =>  DungAF arg -> [arg] -> Bool
let admissible af args =
  // conflictFree af args && args `subset` f af args
  conflictFree af args && subset args (acceptableFwArgs af args)

let [<Test>] ``admissable arguments - argument and counter-argument to is_hard`` () =
  admissible shouldLearn [ "is_fun"; "feeling_of_accomplishment" ] |> Assert.IsTrue
let [<Test>] ``admissable arguments - no counter-argument`` () =
  admissible shouldLearn [ "feeling_of_accomplishment" ] |> Assert.IsTrue
let [<Test>] ``admissable arguments - vacuously true for no arguments`` () =
  admissible shouldLearn [] |> Assert.IsTrue
let [<Test>] ``not admissable arguments - missing counter-argument to is_hard`` () =
  admissible shouldLearn [ "is_fun" ] |> Assert.IsFalse
let [<Test>] ``not admissable arguments - is_hard not conflictFree`` () =
  admissible shouldLearn [ "is_hard" ] |> Assert.IsFalse
let [<Test>] ``not admissable arguments - is_hard not conflictFree'`` () =
  admissible shouldLearn [ "is_fun"; "is_hard" ] |> Assert.IsFalse

// alternatively:
// if 'args' is 'conflictFree' and and each argument in args is acceptable with respect to args.
// admissible af args = conflictFree af args && and [acceptable af arg args | arg <- args]

/// Given a characteristic function f, computes the grounded extension
/// by iterating on the empty set (list) until it reaches a fixpoint.
// fixpoint :: Eq arg => ([arg] -> [arg]) -> [arg]
let fixpoint f =
  let rec groundedF' f args =
    if f args = args then args
    else groundedF' f (f args)
  groundedF' f []

/// Given a list of arguments that are 'Out' in an argumentation framework af,
/// an argument 'arg' is unattacked if the list of its attackers, ignoring the outs, is empty.
/// unattacked :: Eq arg => [arg] -> DungAF arg -> arg -> Bool
let unattacked outs af arg =
  let (AF (_, def)) = af
  let attackers = [for (a, b) in def do if arg = b then yield a]
  List.``null`` (List.cut attackers outs)

let [<Test>] ``unattacked ignore outs`` () =
  unattacked ["feeling_of_accomplishment"] shouldLearn "is_hard" |> Assert.IsTrue

let [<Test>] ``unattacked is false when outs empty and arg is attacked`` () =
  unattacked [] shouldLearn "is_hard" |> Assert.IsFalse

/// Given a list of arguments that are 'In' in an argumentation framework af,
/// an argument 'arg' is attacked if there exists an attacker that is 'In'.
/// attacked :: Eq arg => [arg] -> DungAF arg -> arg -> Bool
let attacked ins af arg =
  let (AF (_, def)) = af
  let attackers =
    def |> List.filter (fun (_, b) -> arg = b)
        |> List.map fst // the first item in the tuples are the attackers
        |> Set.ofList
  not <| Set.isEmpty (attackers |> Set.intersect (Set.ofList ins))

let [<Test>] ``attacked if there exists an attacker in 'ins'`` () =
  attacked ["is_hard"] shouldLearn "is_fun" |> Assert.IsTrue

/// Labelling of arguments.
type Status = In | Out | Undecided
  with override x.ToString() = sprintf "%A" x

/// Computes the grounded labelling for a Dung argumentation framework,
/// returning a list of arguments with statuses.
/// 
/// Based on section 4.1 of Proof Theories and Algorithms for Abstract Argumentation Frameworks
/// by Modgil and Caminada
///grounded :: Eq arg => DungAF arg -> [(arg, Status)]
let grounded af =
  let (AF (args, _)) = af

  /// grounded' :: Eq a => [a] -> [a] ->
  ///              [a] -> DungAF a -> [(a, Status)]
  let rec grounded' = function
    | ins, outs, [], _ ->
      List.map (fun x -> x, In) ins @
      List.map (fun x -> x, Out) outs
    | ins, outs, args, af ->
      let newIns   = List.filter (unattacked outs af)  args
      let newOuts  = List.filter (attacked ins af)     args
      if List.``null`` (newIns @ newOuts)
      then List.map (fun x -> x, In) ins @
           List.map (fun x -> x, Out) outs @
           List.map (fun x -> x, Undecided) args
      else grounded' ((ins @ newIns),
                     (outs @ newOuts),
                     (List.cut args (newIns @ newOuts)),
                     af)

  grounded' ([], [], args, af)

/// The grounded extension of an argumentation framework is just the grounded labelling,
/// keeping only those arguments that were labelled 'In'.
//groundedExt :: Eq arg => DungAF arg -> [arg]
let groundedExt af =
  grounded af
  |> List.filter (function | (_, In) -> true | _ -> false)