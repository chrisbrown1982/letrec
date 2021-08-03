module StructEquiv 

import Letrec
import Decidable.Equality

%default total

mutual 
    implementation Uninhabited (MkEnv [] = MkEnv (_::_)) where
        uninhabited Refl impossible
    implementation Uninhabited (MkEnv (_::_) = MkEnv []) where
        uninhabited Refl impossible

    implementation Equality.DecEq Env where
        decEq (MkEnv []) (MkEnv []) = Yes Refl 
        decEq (MkEnv ((x1, y1)::rest)) (MkEnv ((x2,y2)::rest2)) =
            case decEq x1 x2 of 
                Yes Refl => 
                    case decEq y1 y2 of 
                        Yes Refl => 
                            case decEq rest rest2 of 
                                Yes Refl => Yes Refl 
                                No  neq3 => No (\Refl => neq3 Refl)
                        No  neq2 => No (\Refl => neq2 Refl) 
                No neq => No (\Refl => neq Refl)
        decEq (MkEnv []) (MkEnv (_ :: _)) = No absurd 
        decEq (MkEnv (_ :: _)) (MkEnv []) = No absurd

    implementation Uninhabited (MkClosure _ _ = MkInt _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkClosure _ _ = MkError) where
        uninhabited Refl impossible
    implementation Uninhabited (MkClosure _ _ = MkExpr _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkInt _ = MkClosure _ _ ) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkInt _ = MkError) where
        uninhabited Refl impossible
    implementation Uninhabited (MkInt _ = MkExpr _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkError = MkExpr _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkError = MkClosure _ _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkError = MkInt _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkExpr _ = MkClosure _ _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkExpr _ = MkInt _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkExpr _ = MkError) where 
        uninhabited Refl impossible 

    implementation Equality.DecEq Value where 
        decEq (MkClosure env1 e1) (MkClosure env2 e2) = ?a1 
        decEq (MkInt n1) (MkInt n2) = 
            case decEq n1 n2 of 
                Yes Refl => Yes Refl 
                No  neq  => No (\Refl => neq Refl)
        decEq (MkError) (MkError) = Yes Refl 
        decEq (MkExpr e1) (MkExpr e2) = ?a4

        decEq (MkClosure _ _ ) (MkInt _) = No absurd 
        decEq (MkClosure _ _ ) (MkError) = No absurd 
        decEq (MkClosure _ _ ) (MkExpr _) = No absurd
        decEq (MkInt _) (MkClosure _ _ )  = No absurd 
        decEq (MkInt _) (MkError) = No absurd 
        decEq (MkInt _) (MkExpr _) = No absurd
        decEq (MkError) (MkClosure _ _) = No absurd 
        decEq (MkError) (MkInt _) = No absurd 
        decEq (MkError) (MkExpr _) = No absurd 
        decEq (MkExpr _) (MkClosure _ _) = No absurd 
        decEq (MkExpr _) (MkInt _) = No absurd 
        decEq (MkExpr _) (MkError) = No absurd 
    
{-
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

    implementation Uninhabited (MkVar _ = MkApp _ _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkVar _ = MkVal _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkVar _ = MkBind _ _ _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkVar _ = MkLetRec _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVar _ = MkLam _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVar _ = MkAdd _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVar _ = MkMul _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVar _ = MkMinus _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVar _ = MkIf _ _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkApp _ _ = MkVar _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkApp _ _ = MkVal _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkApp _ _ = MkBind _ _ _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkApp _ _ = MkLetRec _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkApp _ _ = MkLam _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkApp _ _ = MkAdd _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkApp _ _ = MkMul _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkApp _ _ = MkMinus _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkApp _ _= MkIf _ _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVal _ = MkVar _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkVal _ = MkApp _ _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkVal _ = MkBind _ _ _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkVal _ = MkLetRec _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVal _ = MkLam _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVal _ = MkAdd _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVal _ = MkMul _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVal _ = MkMinus _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkVal _= MkIf _ _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkBind _ _ _ = MkVar _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkBind _ _ _ = MkApp _ _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkBind _ _ _ = MkVal _) where 
        uninhabited Refl impossible 
    implementation Uninhabited (MkBind _ _ _ = MkLetRec _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkBind _ _ _ = MkLam _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkBind _ _ _ = MkAdd _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkBind _ _ _ = MkMul _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkBind _ _ _ = MkMinus _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkBind _ _ _= MkIf _ _ _) where 
        uninhabited Refl impossible


    implementation Equality.DecEq Expr where 
        decEq (MkVar v1) (MkVar v2) = 
            case decEq v1 v2 of 
                Yes Refl => Yes Refl 
                No neq   => No (\Refl => neq Refl)

        decEq (MkApp e1 e2) (MkApp e3 e4) = 
            case decEq e1 e3 of 
                Yes Refl => 
                    case decEq e2 e4 of 
                        Yes Refl => Yes Refl  
                        No  neq  => No (\Refl => neq Refl)
                No neq2 => No (\Refl => neq2 Refl)
        decEq (MkVal v1) (MkVal v2) = 
            case decEq v1 v2 of
                Yes Refl => Yes Refl 
                No  neq  => No (\Refl => neq Refl)

        decEq (MkBind v1 e1 e2) (MkBind v2 e3 e4) = 
            case decEq v1 v2 of 
                Yes Refl => 
                    case decEq e1 e3 of 
                        Yes Refl => 
                            case decEq e2 e4 of 
                                Yes Refl => Yes Refl 
                                No  neq  => No (\Refl => neq Refl)
                        No neq2 => No (\Refl => neq2 Refl)
                No neq3 => No (\Refl => neq3 Refl)

        decEq (MkVar _) (MkApp _ _) = No absurd 
        decEq (MkVar _) (MkVal _) = No absurd 
        decEq (MkVar _) (MkBind _ _ _) = No absurd 
        decEq (MkVar _) (MkLetRec _ _) = No absurd 
        decEq (MkVar _) (MkLam _ _) = No absurd 
        decEq (MkVar _) (MkAdd _ _) = No absurd 
        decEq (MkVar _) (MkMul _ _) = No absurd 
        decEq (MkVar _) (MkMinus _ _) = No absurd 
        decEq (MkVar _) (MkIf _ _ _) = No absurd
        decEq (MkApp _ _) (MkVar _) = No absurd 

        decEq (MkApp _ _ ) (MkVal _) = No absurd 
        decEq (MkApp _ _) (MkBind _ _ _) = No absurd 
        decEq (MkApp _ _) (MkLetRec _ _) = No absurd 
        decEq (MkApp _ _) (MkLam _ _) = No absurd 
        decEq (MkApp _ _) (MkAdd _ _) = No absurd 
        decEq (MkApp _ _) (MkMul _ _) = No absurd 
        decEq (MkApp _ _) (MkMinus _ _) = No absurd 
        decEq (MkApp _ _) (MkIf _ _ _) = No absurd

        decEq (MkVal _) (MkVar _) = No absurd
        decEq (MkVal _ ) (MkApp _ _) = No absurd 
        decEq (MkVal _) (MkBind _ _ _) = No absurd 
        decEq (MkVal _) (MkLetRec _ _) = No absurd 
        decEq (MkVal _) (MkLam _ _) = No absurd 
        decEq (MkVal _) (MkAdd _ _) = No absurd 
        decEq (MkVal _) (MkMul _ _) = No absurd 
        decEq (MkVal _) (MkMinus _ _) = No absurd 
        decEq (MkVal _) (MkIf _ _ _) = No absurd 
        
        decEq (MkBind _ _ _ ) (MkVal _) = No absurd 
        decEq (MkBind _ _ _) (MkVar _) = No absurd
        decEq (MkBind _ _ _) (MkApp _ _) = No absurd 
        decEq (MkBind _ _ _) (MkLetRec _ _) = No absurd 
        decEq (MkBind _ _ _) (MkLam _ _) = No absurd 
        decEq (MkBind _ _ _) (MkAdd _ _) = No absurd 
        decEq (MkBind _ _ _) (MkMul _ _) = No absurd 
        decEq (MkBind _ _ _) (MkMinus _ _) = No absurd 
        decEq (MkBind _ _ _) (MkIf _ _ _) = No absurd
        