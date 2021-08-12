module DeBruijn

import Decidable.Equality
import Letrec

%default total

EnvMap : Type 
EnvMap = List (VarName, VarName)

lookup : (v : VarName) -> (env : EnvMap) -> Maybe VarName 
lookup v [] = Nothing 
lookup v ((v1, v2)::rest) = 
    case decEq v v1 of 
        Yes Refl => Just v2 
        No  c    => lookup v rest


{-
     substitutes all free occurrences of X for Y in E 
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
-}
sub : (env : List VarName) -> (x : VarName) -> (y : VarName) -> (e : Expr) -> Expr 
sub env x y (MkVar v) = 
    case elem v env of 
        True => (MkVar v)
        False => case decEq x v of 
                    Yes Refl => (MkVar y)
                    No  c    => (MkVar v)
sub env x y (MkApp e1 e2) = 
    MkApp (sub env x y e1) (sub env x y e2)
sub env x y (MkVal n) = MkVal n 
sub env x y (MkBind v e1 e2) = 
    let env' = v :: env
    in MkBind v (sub env' x y e1) (sub env' x y e2) 
sub env x y (MkLetRec [] e) = 
    MkLetRec [] (sub env x y e)
sub env x y (MkLetRec ((v,e1)::bs) e)  = 
    let env' = v :: env 
        e1'  = sub env' x y e1 
        x    = sub env' x y (MkLetRec bs e)
    in case x of 
        (MkLetRec bs' e') => MkLetRec ((v,e1')::bs') e'
        _                 => MkLetRec ((v,e1)::bs) e
sub env x y (MkLam v e)      = 
    let env' = v :: env
    in MkLam v (sub env' x y e) 
sub env x y (MkAdd e1 e2) = 
    MkAdd (sub env x y e1) (sub env x y e2) 
sub env x y (MkMul e1 e2) = 
    MkMul (sub env x y e1) (sub env x y e2)
sub env x y (MkMinus e1 e2) = 
    MkMinus (sub env x y e1) (sub env x y e2)
sub env x y (MkIf c t e) = 
    MkIf (sub env x y c) (sub env x y t) (sub env x y e)

mutual 

    updateV : (fresh : VarName) -> (v : VarName) -> (bnds : List (VarName, Expr)) -> List (VarName, Expr)
    updateV fresh v [] = [] 
    updateV fresh v ((v1, e)::rest) = 
        case decEq v v1 of 
            Yes Refl => (fresh, e)::(updateV fresh v rest)
            No c => (v1,e)::(updateV fresh v rest)

    deBruijnBnds : (x : VarName) -> (y : VarName) -> (bnds : List (VarName, Expr)) -> List (VarName, Expr)
    deBruijnBnds x y [] = []
    deBruijnBnds x y ((v,e)::bnds) = 
    --    case deBruijn fresh envMap e of 
      --      Left x => Left x
        --    Right e' => 
        case deBruijnBnds x y bnds of
            bnds' => (v,sub [] x y e) :: bnds'

    deBruijnBnds2 : (fresh : Nat) 
                 -- -> (env : EnvMap) 
                 -> (e : Expr) 
                 -> (bnds : List (VarName, Expr)) 
                 -> (mutBnds : List (VarName, Expr)) 
                 -> (Expr, List (VarName, Expr))
    deBruijnBnds2 fresh e bnds [] = (e, bnds) 
    deBruijnBnds2 fresh e bnds ((v,e1)::rest) = 
        let 
            -- envMap' = (v, fresh) :: envMap 
            fresh'  = S fresh
            bnds'   = updateV fresh v bnds 
        in 
            deBruijnBnds2 fresh' (sub [] v fresh e) (deBruijnBnds v fresh bnds') rest 

    export
    deBruijn : (fresh : Nat) 
            -- -> (env : List VarName) 
            -> (e : Expr) 
            -> Expr 
    deBruijn fresh  (MkVar v) = MkVar v
       -- case lookup v envMap of
       --     Nothing => Left ("0" ++ " " ++ (show v) ++ " " ++ (show envMap)) 
       --     Just v2 => Right (MkVar v2)
    deBruijn fresh  (MkApp e1 e2) =
        case deBruijn fresh  e1 of 
            e1' => 
                case deBruijn fresh  e2 of 
                    e2' => MkApp e1' e2'
    deBruijn fresh  (MkVal n) = MkVal n
    deBruijn fresh  (MkBind v e1 e) =
        let fresh' = S fresh 
            e1' = sub [] v fresh e1 
            e'  = sub [] v fresh e 
        in 
            case deBruijn fresh  e1' of 
                e1' => 
                    case deBruijn fresh  e' of 
                        e' => MkBind fresh e1' e'
    deBruijn fresh  (MkLetRec bnds e) =
        case deBruijnBnds2 fresh  e bnds bnds of
            (e', bnds') =>
                case deBruijn fresh e' of 
                    e'' => MkLetRec bnds' e''
    deBruijn fresh  (MkLam v e) = 
        let -- envMap' = (v, fresh) :: envMap 
            fresh'  = S fresh
            e' = sub [] v fresh e
        in 
            case deBruijn fresh e' of
                e' => MkLam fresh e'
    deBruijn fresh  (MkAdd e1 e2) =
        case deBruijn fresh  e1 of 
            e1' => 
                case deBruijn fresh  e2 of 
                   e2' => MkAdd e1' e2'
    deBruijn fresh  (MkMinus e1 e2) =
        case deBruijn fresh  e1 of 
            e1' => 
                case deBruijn fresh  e2 of 
                    e2' => MkMinus e1' e2'
    deBruijn fresh  (MkMul e1 e2) =
        case deBruijn fresh  e1 of 
            e1' => 
                case deBruijn fresh  e2 of 
                   e2' => MkMul e1' e2'
    deBruijn fresh  (MkIf cond th el) = 
        case deBruijn fresh  cond of 
          con' => 
            case deBruijn fresh  th of 
              th' => 
                case deBruijn fresh  el of 
                    el' => MkIf con' th' el'
    -- deBruijn _ _ _ = ?end

