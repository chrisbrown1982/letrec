module InExpr

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

%default total  

mutual 
  public export
  data InValue : Type where 
     MkInInt     : (n : Nat) -> InValue 
     MkInError   : InValue 
     MkInExpr    : (e : InExpr) -> InValue 

  public export
  data InExpr : Type where 
    MkInVar    : (pos : Nat)  -> InExpr
    MkInApp    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkInVal    : (n : Nat) -> InExpr
    MkInBind   : (pos : Nat) -> (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkInLetRec : (pos : List (Nat, InExpr)) -> (e: InExpr) -> InExpr
    MkInLam    : (pos : Nat) -> (e1 : InExpr) -> InExpr
    MkInAdd    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkInMul    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkInMinus  : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkInIf     : (c : InExpr) -> (t : InExpr) -> (el : InExpr) -> InExpr


replaceInEnv : (xs : Vect k t) -> Elem x xs -> t -> Vect k t
replaceInEnv (x::xs)  Here         y = y :: xs
replaceInEnv (x::xs) (There xinxs) y = x :: replaceByElem xs xinxs y

public export
inEval : {n : Nat}
      -> (env : Vect n InValue)
      -> InExpr 
      -> InValue
inEval {n} env (MkInVar pos) with (natToFin pos {n})
    inEval {n} env (MkInVar pos) | Nothing = MkInError
    inEval {n} env (MkInVar pos) | Just l with (index l env)
        inEval {n} env (MkInVar pos) | Just l | val = val

inEval {n} env (MkInApp (MkInLam pos e1) e2) with (inEval env e2) -- evaluate e2 at position prf of env and then evaluate e1 
  inEval {n} env (MkInApp (MkInLam pos e1) e2) | MkInError = MkInError 
  inEval {n} env (MkInApp (MkInLam pos e1) e2) | e2' with (natToFin pos {n})
    inEval {n} env (MkInApp (MkInLam pos e1) e2) | e2' | Nothing = MkInError 
    inEval {n} env (MkInApp (MkInLam pos e1) e2) | e2' | Just l with (replaceAt l e2' env)
      inEval {n} env (MkInApp (MkInLam pos e1) e2) | e2' | Just l | env' = inEval env' e1

inEval env (MkInApp e1 e2) = MkInError 
inEval env (MkInVal n) = MkInInt n

inEval {n} env (MkInBind pos e1 e2) with (inEval env e1) 
  inEval {n} env (MkInBind pos e1 e2) | MkInError = MkInError 
  inEval {n} env (MkInBind pos e1 e2) | e1' with (natToFin pos {n})
    inEval {n} env (MkInBind pos e1 e2) | e1' | Nothing = MkInError 
    inEval {n} env (MkInBind pos e1 e2) | e1' | Just l with (replaceAt l e1' env) 
      inEval {n} env (MkInBind pos e1 e2) | e1' | Just l | env' = inEval env' e2

inEval env (MkInLam prf e1) = MkInError 

inEval env (MkInAdd e1 e2) with (inEval env e1)
  inEval env (MkInAdd e1 e2) | MkInInt e1' with (inEval env e2) 
    inEval env (MkInAdd e1 e2) | MkInInt e1' | MkInInt e2' = MkInInt (plus e1' e2')
    inEval env (MkInAdd e1 e2) | MkInInt e1' | _ = MkInError  
  inEval env (MkInAdd e1 e2) | _ = MkInError 

inEval env (MkInMul e1 e2) with (inEval env e1)
  inEval env (MkInMul e1 e2) | MkInInt e1' with (inEval env e2) 
    inEval env (MkInMul e1 e2) | MkInInt e1' | MkInInt e2' = MkInInt (mult e1' e2')
    inEval env (MkInMul e1 e2) | MkInInt e1' | _ = MkInError 
  inEval env (MkInMul e1 e2) | _ = MkInError 

inEval env (MkInMinus e1 e2) with (inEval env e1)
  inEval env (MkInMinus e1 e2) | MkInInt e1' with (inEval env e2) 
    inEval env (MkInMinus e1 e2) | MkInInt e1' | MkInInt e2' = MkInInt (minus e1' e2')
    inEval env (MkInMinus e1 e2) | MkInInt e1' | _ = MkInError 
  inEval env (MkInMinus e1 e2) | _ = MkInError 

inEval env (MkInIf c t el) with (inEval env c)
  inEval env (MkInIf c t el) | MkInInt c' =
    if c'==0 then inEval env el else inEval env t 
  inEval env (MkInIf c t el) | _ = MkInError
-- inEval _ (MkLetRec _ _) = ?hole

inEval env (MkInLetRec [] e) = inEval env e 

inEval {n} env (MkInLetRec ((pos, e1)::bnds) e) with (natToFin pos {n})
    inEval {n} env (MkInLetRec ((pos, e1)::bnds) e) | Nothing = MkInError 
    inEval {n} env (MkInLetRec ((pos, e1)::bnds) e) | Just l with (replaceAt l (MkInExpr e1) env)
      inEval {n} env (MkInLetRec ((pos, e1)::bnds) e) | Just l | env' = (assert_total (inEval env' (MkInLetRec bnds e)))
