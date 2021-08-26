module InExpr

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

%default total    

public export
data InExpr : Type where 
    MkVar    : (prf : Elem v e)  -> InExpr
    MkApp    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkVal    : (n : Nat) -> InExpr
    MkBind   : (prf : Elem v e) -> (e1 : InExpr) -> (e2 : InExpr) -> InExpr
  --  MkLetRec : (bs : List (VarName, Expr)) -> (e : Expr) -> Expr 
  --  MkLetRec : (prfs : List profs) -> list exprs -> expr -> ...
    MkLam    : (prf : Elem v e) -> (e1 : InExpr) -> InExpr
    MkAdd    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkMul    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkMinus  : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkIf     : (c : InExpr) -> (t : InExpr) -> (el : InExpr) -> InExpr


replaceInEnv : (xs : Vect k t) -> Elem x xs -> t -> Vect k t
replaceInEnv (x::xs)  Here         y = y :: xs
replaceInEnv (x::xs) (There xinxs) y = x :: replaceByElem xs xinxs y


inEval : 
         (env : Vect n Nat)
      -> InExpr 
      -> Maybe Nat 
inEval env (MkVar prf) with (elemToFin prf)
    inEval env (MkVar prf) | l with (indexElem l env)
        inEval env (MkVar prf) | l | (val ** prf2) = Just val
inEval env (MkApp (MkLam {env2} prf e1) e2) with (inEval env e2) -- evaluate e2 at position prf of env and then evaluate e1 
  inEval env (MkApp (MkLam {env2} prf e1) e2) | Nothing = Nothing 
  inEval env (MkApp (MkLam {env2} prf e1) e2) | Just e2' with (replaceInEnv env prf e2')
    inEval env (MkApp (MkLam {env2} prf e1) e2) | Just e2' | env' with (inEval env' e1)
      inEval env (MkApp (MkLam {env2=env'} prf e1) e2) | Just e2' | env' | e1' = ?hole
inEval env (MkApp e1 e2) = Nothing 
inEval env (MkVal n) = Just n
inEval env (MkBind prf e1 e2) = ?h3
inEval env (MkLam prf e1) = ?h4 
inEval env (MkAdd e1 e2) with (inEval env e1)
  inEval env (MkAdd e1 e2) | Nothing = Nothing 
  inEval env (MkAdd e1 e2) | Just e1' with (inEval env e2) 
    inEval env (MkAdd e1 e2) | Just e1' | Just e2' = Just (plus e1' e2')
    inEval env (MkAdd e1 e2) | Just e1' | Nothing = Nothing  
inEval env (MkMul e1 e2) with (inEval env e1)
  inEval env (MkMul e1 e2) | Nothing = Nothing 
  inEval env (MkMul e1 e2) | Just e1' with (inEval env e2) 
    inEval env (MkMul e1 e2) | Just e1' | Just e2' = Just (mult e1' e2')
    inEval env (MkMul e1 e2) | Just e1' | Nothing = Nothing 
inEval env (MkMinus e1 e2) with (inEval env e1)
  inEval env (MkMinus e1 e2) | Nothing = Nothing 
  inEval env (MkMinus e1 e2) | Just e1' with (inEval env e2) 
    inEval env (MkMinus e1 e2) | Just e1' | Just e2' = Just (minus e1' e2')
    inEval env (MkMinus e1 e2) | Just e1' | Nothing = Nothing 
inEval env (MkIf c t el) = ?h8
