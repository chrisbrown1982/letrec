module InExpr

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

%default total  

mutual 
  public export
  data InValue : Type where 
     MkInt     : (n : Nat) -> InValue 
     MkError   : InValue 
     MkInExpr    : (e : InExpr) -> InValue 

  public export
  data InExpr : Type where 
    MkVar    : (pos : Nat)  -> InExpr
    MkApp    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkVal    : (n : Nat) -> InExpr
    MkBind   : (pos : Nat) -> (e1 : InExpr) -> (e2 : InExpr) -> InExpr
  --  MkLetRec : (bs : List (VarName, Expr)) -> (e : Expr) -> Expr 
    MkLetRec : (pos : List (Nat, InExpr)) -> (e: InExpr) -> InExpr
    MkLam    : (pos : Nat) -> (e1 : InExpr) -> InExpr
    MkAdd    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkMul    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkMinus  : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkIf     : (c : InExpr) -> (t : InExpr) -> (el : InExpr) -> InExpr


replaceInEnv : (xs : Vect k t) -> Elem x xs -> t -> Vect k t
replaceInEnv (x::xs)  Here         y = y :: xs
replaceInEnv (x::xs) (There xinxs) y = x :: replaceByElem xs xinxs y


inEval : {n : Nat}
      -> (env : Vect n InValue)
      -> InExpr 
      -> InValue
inEval {n} env (MkVar pos) with (natToFin pos {n})
    inEval {n} env (MkVar pos) | Nothing = MkError
    inEval {n} env (MkVar pos) | Just l with (index l env)
        inEval {n} env (MkVar pos) | Just l | val = val

inEval {n} env (MkApp (MkLam pos e1) e2) with (inEval env e2) -- evaluate e2 at position prf of env and then evaluate e1 
  inEval {n} env (MkApp (MkLam pos e1) e2) | MkError = MkError 
  inEval {n} env (MkApp (MkLam pos e1) e2) | e2' with (natToFin pos {n})
    inEval {n} env (MkApp (MkLam pos e1) e2) | e2' | Nothing = MkError 
    inEval {n} env (MkApp (MkLam pos e1) e2) | e2' | Just l with (replaceAt l e2' env)
      inEval {n} env (MkApp (MkLam pos e1) e2) | e2' | Just l | env' = inEval env' e1

inEval env (MkApp e1 e2) = MkError 
inEval env (MkVal n) = MkInt n

inEval {n} env (MkBind pos e1 e2) with (inEval env e1) 
  inEval {n} env (MkBind pos e1 e2) | MkError = MkError 
  inEval {n} env (MkBind pos e1 e2) | e1' with (natToFin pos {n})
    inEval {n} env (MkBind pos e1 e2) | e1' | Nothing = MkError 
    inEval {n} env (MkBind pos e1 e2) | e1' | Just l with (replaceAt l e1' env) 
      inEval {n} env (MkBind pos e1 e2) | e1' | Just l | env' = inEval env' e2

inEval env (MkLam prf e1) = MkError 

inEval env (MkAdd e1 e2) with (inEval env e1)
  inEval env (MkAdd e1 e2) | MkInt e1' with (inEval env e2) 
    inEval env (MkAdd e1 e2) | MkInt e1' | MkInt e2' = MkInt (plus e1' e2')
    inEval env (MkAdd e1 e2) | MkInt e1' | _ = MkError  
  inEval env (MkAdd e1 e2) | _ = MkError 

inEval env (MkMul e1 e2) with (inEval env e1)
  inEval env (MkMul e1 e2) | MkInt e1' with (inEval env e2) 
    inEval env (MkMul e1 e2) | MkInt e1' | MkInt e2' = MkInt (mult e1' e2')
    inEval env (MkMul e1 e2) | MkInt e1' | _ = MkError 
  inEval env (MkMul e1 e2) | _ = MkError 

inEval env (MkMinus e1 e2) with (inEval env e1)
  inEval env (MkMinus e1 e2) | MkInt e1' with (inEval env e2) 
    inEval env (MkMinus e1 e2) | MkInt e1' | MkInt e2' = MkInt (minus e1' e2')
    inEval env (MkMinus e1 e2) | MkInt e1' | _ = MkError 
  inEval env (MkMinus e1 e2) | _ = MkError 

inEval env (MkIf c t el) with (inEval env c)
  inEval env (MkIf c t el) | MkInt c' =
    if c'==0 then inEval env el else inEval env t 
  inEval env (MkIf c t el) | _ = MkError
-- inEval _ (MkLetRec _ _) = ?hole

inEval env (MkLetRec [] e) = inEval env e 

inEval {n} env (MkLetRec ((pos, e1)::bnds) e) with (natToFin pos {n})
    inEval {n} env (MkLetRec ((pos, e1)::bnds) e) | Nothing = MkError 
    inEval {n} env (MkLetRec ((pos, e1)::bnds) e) | Just l with (replaceAt l (MkInExpr e1) env)
      inEval {n} env (MkLetRec ((pos, e1)::bnds) e) | Just l | env' with (assert_total (inEval env' (MkLetRec bnds e)))
        inEval {n} env (MkLetRec ((pos, e1)::bnds) e) | Just l | env' | e' = ?hole