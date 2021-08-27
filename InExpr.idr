module InExpr

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality
import Letrec

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
    MkInVal    : (n : InValue) -> InExpr
    MkInBind   : (pos : Nat) -> (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkInLetRec : (pos : List (Nat, InExpr)) -> (e: InExpr) -> InExpr
    MkInLam    : (pos : Nat) -> (e1 : InExpr) -> InExpr
    MkInAdd    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkInMul    : (e1 : InExpr) -> (e2 : InExpr) -> InExpr
    MkInMinus  : (e1 : InExpr) -> (e2 : InExpr) -> InExpr 
    MkInIf     : (c : InExpr) -> (t : InExpr) -> (el : InExpr) -> InExpr

public export
indExp' : Nat -> Expr -> (Nat, InExpr) 
indExp' n (MkVar v) = (S n, MkInVar n)
indExp' n (MkApp e1 e2) with (indExp' n e1) 
  indExp' n (MkApp e1 e2) | (n', e1') with (indExp' n' e2)
    indExp' n (MkApp e1 e2) | (n', e1') | (n'', e2') = (n'', MkInApp e1' e2')
indExp' n (MkVal (MkInt n1)) = (n, MkInVal (MkInInt n1))
indExp' n (MkVal (MkExpr e)) with (indExp' n e) 
  indExp' n (MkVal (MkExpr e)) | (n', e') = (n', MkInVal (MkInExpr e'))
indExp' n (MkVal (MkClosure _ _)) = (n, MkInVal MkInError)
indExp' n (MkVal MkError) = (n, MkInVal MkInError)
indExp' n (MkBind v e1 e2) with (indExp' (S n) e1)
  indExp' n (MkBind v e1 e2) | (n', e1') with (indExp' n' e2)
    indExp' n (MkBind v e1 e2) | (n', e1') | (n'', e2') = (n'', MkInBind n e1' e2')
indExp' n (MkLetRec [] e) with (indExp' n e)
  indExp' n (MkLetRec [] e) | (n', e') = (n', MkInLetRec [] e')
indExp' n (MkLetRec ((v, e)::bs) e2) with (indExp' (S n) e) 
  indExp' n (MkLetRec ((v, e)::bs) e2) | (n', e') with (assert_total (indExp' n' (MkLetRec bs e2)))
    indExp' n (MkLetRec ((v, e)::bs) e2) | (n', e') | (n'', MkInLetRec bs' e2') = (n'', MkInLetRec ((n, e')::bs') e2') 
    indExp' n (MkLetRec ((v, e)::bs) e2) | (n', e') | (n'', _) = (n'', MkInVal MkInError)
indExp' n (MkLam b e1) with (indExp' (S n) e1)
  indExp' n (MkLam b e1) | (n', e1') = (n', MkInLam n e1')
indExp' n (MkAdd e1 e2) with (indExp' n e1) 
  indExp' n (MkAdd e1 e2) | (n', e1') with (indExp' n' e2)
    indExp' n (MkAdd e1 e2) | (n', e1') | (n'', e2') = (n'', MkInAdd e1' e2')
indExp' n (MkMul e1 e2) with (indExp' n e1) 
  indExp' n (MkMul e1 e2) | (n', e1') with (indExp' n' e2)
    indExp' n (MkMul e1 e2) | (n', e1') | (n'', e2') = (n'', MkInMul e1' e2')
indExp' n (MkMinus e1 e2) with (indExp' n e1) 
  indExp' n (MkMinus e1 e2) | (n', e1') with (indExp' n' e2)
    indExp' n (MkMinus e1 e2) | (n', e1') | (n'', e2') = (n'', MkInMinus e1' e2')
indExp' n (MkIf c t e) with (indExp' n c) 
  indExp' n (MkIf c t e) | (n', c') with (indExp' n' t) 
    indExp' n (MkIf c t e) | (n', c') | (n'', t') with (indExp' n'' e) 
      indExp' n (MkIf c t e) | (n', c') | (n'', t') | (n''', e') = (n''', MkInIf c' t' e')

public export 
indExp : Nat -> Expr -> InExpr 
indExp n e with (indExp' n e) 
  indExp n e | (n', e') = e'


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
inEval env (MkInVal e) = e

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
