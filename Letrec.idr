module Letrec

import Decidable.Equality

%default total

public export 
VarName : Type 
VarName = Nat 

mutual
    public export 
    data Env : Type where 
       MkEnv : List (VarName, Value) -> Env

    public export 
    data Value : Type where 
       MkClosure : (env : Env) -> (e : Expr) -> Value 
       MkInt     : (n : Nat) -> Value 
       MkError   : Value 
       MkExpr    : (e : Expr) -> Value 

    public export
    data Expr : Type where 
        MkVar    : (v : VarName) -> Expr 
        MkApp    : (e1 : Expr) -> (e2 : Expr) -> Expr 
        MkVal    : (n : Value) -> Expr 
        MkBind   : (v : VarName) -> (e1 : Expr) -> (e2 : Expr) -> Expr 
        MkLetRec : (bs : List (VarName, Expr)) -> (e : Expr) -> Expr 
        MkLam    : (v : VarName) -> (e : Expr) -> Expr 
        MkAdd    : (e1 : Expr) -> (e2 : Expr) -> Expr 
        MkMul    : (e1 : Expr) -> (e2 : Expr) -> Expr
        MkMinus  : (e1 : Expr) -> (e2 : Expr) -> Expr 
        MkIf     : (c : Expr) -> (t : Expr) -> (e : Expr) -> Expr

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

    export
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
    eval env (MkAdd e1 e2) =
        case eval env e1 of 
            MkInt v1 => 
                case eval env e2 of 
                    MkInt v2 => MkInt (plus v1 v2)
                    _        => MkError
            _ => MkError 
    eval env (MkMul e1 e2) =
        case eval env e1 of 
            MkInt v1 => 
                case eval env e2 of 
                    MkInt v2 => MkInt (mult v1 v2)
                    _        => MkError
            _ => MkError 
    eval env (MkMinus e1 e2) =
            case eval env e1 of 
                MkInt v1 => 
                    case eval env e2 of 
                        MkInt v2 => MkInt (minus v1 v2)
                        _        => MkError
                _ => MkError 
    eval env (MkIf cond th el) =
        case eval env cond of 
            MkInt n => if n==0 then eval env el else eval env th 
            _       => MkError 

export
t1 : Expr 
t1 = MkLetRec [ (0, MkLam 1 (MkIf (MkVar 1) (MkMul (MkVar 1) (MkApp (MkVar 0) (MkMinus (MkVar 1) (MkVal (MkInt 1))))) (MkVal (MkInt 1)))) ]
              (MkApp (MkVar 0) (MkVal (MkInt 5)))

export
t2 : Expr 
t2 = (MkLetRec [(5, MkVal (MkInt 1))] (MkAdd (MkVar 5) (MkVal (MkInt 3))))

export
t3 : Expr 
t3 = (MkLetRec [(5, MkVal (MkInt 1)), (4, (MkVal (MkInt 1)))] (MkAdd (MkVar 5) (MkVal (MkInt 3))))

export 
t4 : Expr 
t4 = (MkLetRec [(5, MkVal (MkInt 1)), (4, (MkVal (MkInt 1)))] (MkApp (MkLam 5 (MkVar 5) ) (MkAdd (MkVar 5) (MkVal (MkInt 3)))  )  )

export 
t5 : Expr  
t5 = (MkLetRec [(5, MkVal (MkInt 1)), (4, (MkVal (MkInt 1)))] (MkBind 5 (MkAdd (MkVar 5) (MkVal (MkInt 3))) (MkVar 5) )  )

export 
t6 : Expr  
t6 = (MkLetRec [(5, MkVal (MkInt 1)), (4, (MkVal (MkInt 1)))] (MkBind 5 (MkApp (MkLam 5 (MkVar 5) ) (MkAdd (MkVar 5) (MkVal (MkInt 3)))  ) (MkVar 5) )  )