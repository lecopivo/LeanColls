/- Copyright (c) 2023 Tomáš Skřivan.

Authors: Tomáš Skřivan
-/

import LeanColls.Classes.Indexed.Basic

namespace LeanColls

/-! ## Notation for Indexed Collections

This file defines notation:
 - `x[i,j,k]` for getting elements
 - `x[i,j,k] := xi` for setting elements
-/


namespace Indexed.Notation

open Lean Meta


open Lean Elab Term Meta in
@[inherit_doc getElem]
elab:max (priority:=high) x:term noWs "[" i:term "]" : term => do
  try
    let x ← elabTerm x none
    let X ← inferType x
    let Idx ← mkFreshTypeMVar
    let Elem ← mkFreshTypeMVar
    let cls := (mkAppN (← mkConstWithFreshMVarLevels ``GetElem') #[X, Idx, Elem])
    let _ ← synthInstance cls
    let Dom ← mkFreshExprMVar none
    let cls := (mkAppN (← mkConstWithFreshMVarLevels ``GetElem) #[X, (← instantiateMVars Idx), Elem, Dom])
    let instGetElem ← synthInstance cls
    let i ← elabTerm i Idx
    let dom ← mkFreshExprMVar (mkAppN Dom #[x,i])
    dom.mvarId!.assign (.const ``True.intro [])
    return ← mkAppOptM ``getElem #[X,Idx,Elem,Dom,instGetElem,x,i,dom]
  catch _ =>
    return ← elabTerm (← `(getElem $x $i (by get_elem_tactic))) none



/-- Turn an array of terms in into a tuple. -/
private def mkTuple (xs : Array (TSyntax `term)) : MacroM (TSyntax `term) :=
  `(term| ($(xs[0]!), $(xs[1:]),*))


/-- Element index can either be an index or a range. -/
syntax elemIndex := (term)? (":" (term)?)?


/--
The syntax `x[i,j,k]` gets the element of `x : X` indexed by `(i,j,k)`. It is required that there is
an instance `Indexed X I E` and `(i,j,k)` has type `I`.

This notation also support ranges, `x[:i,j₁:j₂,k]` returns a slice of `x`.

Note that product is right associated thus `x[i,j,k]`, `x[i,(j,k)]` and `x[(i,j,k)]` result in
the same expression.
-/
macro:max (name:=indexedGet) (priority:=high+1) x:term noWs "[" i:term ", " is:term,* "]" : term => do
  let idx ← mkTuple (#[i] ++ is.getElems)
  `($x[$idx])

-- todo: merge with `indexedGet`
--       right now I could not figure out how to correctly write down the corresponding macro_rules
@[inherit_doc indexedGet]
syntax:max (name:=indexedGetRanges) (priority:=high) term noWs "[" elemIndex "," elemIndex,* "]" : term


macro (priority:=high) x:ident noWs "[" ids:term,* "]" " := " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.set $x $i $xi)

macro (priority:=high) x:ident noWs "[" ids:term,* "]" " ← " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.set $x $i (← $xi))

macro x:ident noWs "[" ids:term,* "]" " += " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi + $xi))

macro x:ident noWs "[" ids:term,* "]" " -= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi - $xi))

macro x:ident noWs "[" ids:term,* "]" " *= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi * $xi))

macro x:ident noWs "[" ids:term,* "]" " /= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => xi / $xi))

macro x:ident noWs "[" ids:term,* "]" " •= " xi:term : doElem => do
  let i ← mkTuple ids.getElems
  `(doElem| $x:ident := Indexed.update $x $i (fun xi => $xi • xi))


@[app_unexpander GetElem.getElem] def unexpandIndexedGet : Lean.PrettyPrinter.Unexpander
  | `($(_) $x ($i, $is,*) $_) => `($x[$i:term,$[$is:term],*])
  | _ => throw ()
