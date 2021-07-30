module Letrec2

import Decidable.Equality

%default total

VarName : Type 
VarName = Nat 

mutual
    data Env : Type where 
       MkEnv : List (VarName, Value) -> Env

    data Value : Type where 
       MkClosure : (env : Env) -> (e : Expr) -> Value 
       MkInt     : (n : Nat) -> Value 
       MkError   : Value 
       MkExpr    : (e : Expr) -> Value 

    data Expr : Type where 
        MkVar    : (v : VarName) -> Expr 
        MkApp    : (e1 : Expr) -> (e2 : Expr) -> Expr 
        MkVal    : (n : Value) -> Expr 
        MkBind   : (v : VarName) -> (e1 : Expr) -> (e2 : Expr) -> Expr 
        MkLetRec : (bs : List (VarName, Expr)) -> (e : Expr) -> Expr 
        MkLam    : (v : VarName) -> (e : Expr) -> Expr 

lookup : (v : VarName) -> (env : Env) -> Maybe Value 
lookup v (MkEnv []) = Nothing 
lookup v (MkEnv ((var, val)::rest)) = 
    case decEq v var of 
        Yes Refl => Just val 
        No  c    => assert_total (lookup v (MkEnv rest))

mutual 
    newEnv : (env : List (VarName, Value)) -> (bnds : List (VarName, Expr)) -> List (VarName, Value)
    newEnv env []                       = env
    newEnv env ((n, e)::bnds) = 
        let t1 = (n, eval (MkEnv env) e) 
        in  assert_total (newEnv (t1 :: env)  bnds)     

    eval : (env : Env) -> (e : Expr) -> Value 
    eval env (MkVal n) = n 
    eval env (MkVar v) = 
        case lookup v env of 
            Just (MkExpr e') => assert_total (eval env e')
            Just val         => val  
               
            Nothing  => MkError  
    eval env (MkLam v e) = MkClosure env (MkLam v e)
    eval (MkEnv env) (MkApp e1 e2) = 
        let v1 = eval (MkEnv env) e1 
            v2 = eval (MkEnv env) e2 
        in case v1 of 
            MkClosure env1 (MkLam x e) => assert_total (eval (MkEnv ((x,v2)::env)) e)
            _ => MkError 
    eval (MkEnv env) (MkBind x1 e1 e) = 
        let v    = eval (MkEnv env) e1
            env' = MkEnv ((x1, v)::env)
        in eval env' e
    eval (MkEnv env) (MkLetRec bnds body) =
        let bnds' = map (\(n, e) => (n, MkExpr e)) bnds 
        in eval (MkEnv (bnds'++env)) body 


        -- let env' = [(n, eval env' e) | (n, e) <- bnds] ++ env
        -- in ?hole -- eval (MkEnv env') body

        -- let env' = MkEnv (newEnv env bnds ++ env)
        -- in eval env' body
