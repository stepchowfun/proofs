(****************************)
(****************************)
(****                    ****)
(****   Free variables   ****)
(****                    ****)
(****************************)
(****************************)

Require Import List.
Require Import Main.SystemF.Syntax.

Import ListNotations.

Fixpoint eeFreeVars e1 :=
  match e1 with
  | eFreeVar x => [x]
  | eBoundVar _ => []
  | eAbs _ e2 => eeFreeVars e2
  | eApp e2 e3 => eeFreeVars e2 ++ eeFreeVars e3
  | eTAbs e2 => eeFreeVars e2
  | eTApp e2 _ => eeFreeVars e2
  end.

Fixpoint tFreeVars t1 :=
  match t1 with
  | tFreeVar x => [x]
  | tBoundVar _ => []
  | tArrow t2 t3 => tFreeVars t2 ++ tFreeVars t3
  | tForAll t2 => tFreeVars t2
  end.

Fixpoint etFreeVars e1 :=
  match e1 with
  | eFreeVar x => []
  | eBoundVar _ => []
  | eAbs t e2 => tFreeVars t ++ etFreeVars e2
  | eApp e2 e3 => etFreeVars e2 ++ etFreeVars e3
  | eTAbs e2 => etFreeVars e2
  | eTApp e2 t => etFreeVars e2 ++ tFreeVars t
  end.
