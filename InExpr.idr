module InExpr

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

%default total    

mutual 
    public export
    data InExpr : (e: Vect n Nat) -> Type where 
        MkVar    : (prf : Elem v e)  -> InExpr e
        MkApp    : (e1 : InExpr e) -> (e2 : InExpr e) -> InExpr e 
        MkVal    : (n : Nat) -> InExpr e 
        MkBind   : (prf : Elem v env2) -> (e1 : InExpr env) -> (e2 : InExpr env2) -> InExpr env
        --  MkLetRec : (bs : List (VarName, Expr)) -> (e : Expr) -> Expr 
        --  MkLetRec : (prfs : List profs) -> list exprs -> expr -> ...
        MkLam    : (prf : Elem v e2) -> (e1 : InExpr e2) -> InExpr e 
        MkAdd    : (e1 : InExpr e) -> (e2 : InExpr e) -> InExpr e 
        MkMul    : (e1 : InExpr e) -> (e2 : InExpr e) -> InExpr e
        MkMinus  : (e1 : InExpr e) -> (e2 : InExpr e) -> InExpr e 
        MkIf     : (c : InExpr e) -> (t : InExpr e) -> (el : InExpr e) -> InExpr e

    inEval : 
             (env : Vect n Nat)
          -> (InExpr env) 
          -> Nat 
    inEval env (MkVar prf) with (elemToFin prf)
        inEval env (MkVar prf) | l with (indexElem l env)
            inEval env (MkVar prf) | l | (val ** prf2) = val
    inEval env (MkApp e1 e2) = ?h2
    inEval env (MkVal n) = n
    -- let prf = e1 in e2
    inEval env (MkBind {env2} prf e1 e2) with (inEval env e1)
        inEval env (MkBind {env2} prf e1 e2) | e1' with (inEval ..)
    inEval env (MkLam prf e1) = ?h4 
    inEval env (MkAdd e1 e2) = plus (inEval env e1) (inEval env e2) 
    inEval env (MkMul e1 e2) = mult (inEval env e2) (inEval env e2) 
    inEval env (MkMinus e1 e2) = minus (inEval env e1) (inEval env e2) 
    inEval env (MkIf c t el) = ?h8