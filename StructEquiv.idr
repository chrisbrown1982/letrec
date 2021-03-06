module StructEquiv 

import Letrec
import DeBruijn
import Decidable.Equality
import InExpr
import Data.Vect

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
    implementation Uninhabited (MkLetRec _ _ = MkVar _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkApp _ _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkVal _) where 
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkBind _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkLam _ _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkAdd _ _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkMul _ _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkMinus _ _) where
        uninhabited Refl impossible
    implementation Uninhabited (MkLetRec _ _ = MkIf _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkVar _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkApp _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkVal _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkBind _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkLetRec _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkAdd _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkMul _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkMinus _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkLam _ _ = MkIf _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkVar _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkApp _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkVal _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkBind _ _ _) where    
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkLetRec _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkLam _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkMul _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkMinus _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkAdd _ _ = MkIf _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkVar _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkApp _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkVal _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkBind _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkLetRec _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkLam _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkAdd _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkMinus _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMul _ _ = MkIf _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkVar _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkApp _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkVal _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkBind _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkLetRec _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkLam _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkAdd _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkMul _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkMinus _ _ = MkIf _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkVar _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkApp _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkVal _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkBind _ _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkLetRec _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkLam _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkAdd _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkMul _ _) where
        uninhabited Refl impossible
    implementation Uninhabited  (MkIf _ _ _ = MkMinus _ _) where
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

        decEq (MkLetRec bnds1 e1) (MkLetRec bnds2 e2) = 
            case decEq bnds1 bnds2 of 
                Yes Refl => 
                    case decEq e1 e2 of 
                        Yes Refl => Yes Refl 
                        No  neq1 => No (\Refl => neq1 Refl)
                No  neq  => No (\Refl => neq Refl)

        decEq (MkLam v1 e1) (MkLam v2 e2) = 
            case decEq v1 v2 of 
                Yes Refl => 
                    case decEq e1 e2 of 
                        Yes Refl => Yes Refl 
                        No neq   => No (\Refl => neq Refl)
                No neq2 => No (\Refl => neq2 Refl)

        decEq (MkAdd e1 e2) (MkAdd e3 e4) = 
            case decEq e1 e3 of 
                Yes Refl => 
                    case decEq e2 e4 of 
                        Yes Refl => Yes Refl 
                        No neq   => No (\Refl => neq Refl)
                No neq2 => No (\Refl => neq2 Refl) 
        
        decEq (MkMul e1 e2) (MkMul e3 e4) = 
            case decEq e1 e3 of 
                Yes Refl => 
                    case decEq e2 e4 of 
                        Yes Refl => Yes Refl 
                        No neq   => No (\Refl => neq Refl)
                No neq2 => No (\Refl => neq2 Refl) 

        decEq (MkMinus e1 e2) (MkMinus e3 e4) = 
            case decEq e1 e3 of 
                Yes Refl => 
                    case decEq e2 e4 of 
                        Yes Refl => Yes Refl 
                        No neq   => No (\Refl => neq Refl)
                No neq2 => No (\Refl => neq2 Refl)

        decEq (MkIf c1 e1 e2) (MkIf c2 e3 e4) = 
            case decEq c1 c2 of 
                Yes Refl => 
                    case decEq e1 e3 of 
                        Yes Refl => 
                            case decEq e2 e4 of 
                                Yes Refl => Yes Refl 
                                No neq => No (\Refl => neq Refl)
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
        decEq (MkLetRec _ _) (MkVar _) = No absurd
        decEq (MkLetRec _ _) (MkApp _ _) = No absurd
        decEq (MkLetRec _ _) (MkVal _) = No absurd
        decEq (MkLetRec _ _) (MkBind _ _ _) = No absurd
        decEq (MkLetRec _ _) (MkLam _ _) = No absurd
        decEq (MkLetRec _ _) (MkAdd _ _) = No absurd
        decEq (MkLetRec _ _) (MkMul _ _) = No absurd
        decEq (MkLetRec _ _) (MkMinus _ _) = No absurd
        decEq (MkLetRec _ _) (MkIf _ _ _) = No absurd
        decEq (MkLam _ _) (MkVar _) = No absurd
        decEq (MkLam _ _) (MkApp _ _) = No absurd
        decEq (MkLam _ _) (MkVal _) = No absurd
        decEq (MkLam _ _) (MkBind _ _ _) = No absurd
        decEq (MkLam _ _) (MkLetRec _ _) = No absurd
        decEq (MkLam _ _) (MkAdd _ _) = No absurd
        decEq (MkLam _ _) (MkMul _ _) = No absurd
        decEq (MkLam _ _) (MkMinus _ _) = No absurd
        decEq (MkLam _ _) (MkIf _ _ _) = No absurd
        decEq (MkAdd _ _) (MkVar _) = No absurd
        decEq (MkAdd _ _) (MkApp _ _) = No absurd
        decEq (MkAdd _ _) (MkVal _) = No absurd
        decEq (MkAdd _ _) (MkBind _ _ _) = No absurd
        decEq (MkAdd _ _) (MkLetRec _ _) = No absurd
        decEq (MkAdd _ _) (MkLam _ _) = No absurd
        decEq (MkAdd _ _) (MkMul _ _) = No absurd
        decEq (MkAdd _ _) (MkMinus _ _) = No absurd
        decEq (MkAdd _ _) (MkIf _ _ _) = No absurd
        decEq (MkMul _ _) (MkVar _) = No absurd
        decEq (MkMul _ _) (MkApp _ _) = No absurd
        decEq (MkMul _ _) (MkVal _) = No absurd
        decEq (MkMul _ _) (MkBind _ _ _) = No absurd
        decEq (MkMul _ _) (MkLetRec _ _) = No absurd
        decEq (MkMul _ _) (MkLam _ _) = No absurd
        decEq (MkMul _ _) (MkAdd _ _) = No absurd
        decEq (MkMul _ _) (MkMinus _ _) = No absurd
        decEq (MkMul _ _) (MkIf _ _ _) = No absurd
        decEq (MkMinus _ _) (MkVar _) = No absurd
        decEq (MkMinus _ _) (MkApp _ _) = No absurd
        decEq (MkMinus _ _) (MkVal _) = No absurd
        decEq (MkMinus _ _) (MkBind _ _ _) = No absurd
        decEq (MkMinus _ _) (MkLetRec _ _) = No absurd
        decEq (MkMinus _ _) (MkLam _ _) = No absurd
        decEq (MkMinus _ _) (MkAdd _ _) = No absurd
        decEq (MkMinus _ _) (MkMul _ _) = No absurd
        decEq (MkMinus _ _) (MkIf _ _ _) = No absurd
        decEq (MkIf _ _ _) (MkVar _) = No absurd
        decEq (MkIf _ _ _) (MkApp _ _) = No absurd
        decEq (MkIf _ _ _) (MkVal _) = No absurd
        decEq (MkIf _ _ _) (MkBind _ _ _) = No absurd
        decEq (MkIf _ _ _) (MkLetRec _ _) = No absurd
        decEq (MkIf _ _ _) (MkLam _ _) = No absurd
        decEq (MkIf _ _ _) (MkAdd _ _) = No absurd
        decEq (MkIf _ _ _) (MkMul _ _) = No absurd
        decEq (MkIf _ _ _) (MkMinus _ _) = No absurd

{-
data Rename : (lvl : Nat) -> (id : Nat) -> (oldN : Name Variable) -> (newN : Name Variable) -> (m1, m2: Hs98.HsModuleTy.HsModuleTy) -> Type where
  MkRename :   DecldHsModuleTy lvl id oldN m1 
            -> DecldHsModuleTy lvl id newN m2 
            -> Struct m1 m1' -> Struct m2 m2' -> m1' = m2' -> Rename lvl id oldN newN m1 m2
-}

data StructEquiv : (p1, p2 : Expr) -> Type where 
    MkStructEquiv : p1 = p2 -> StructEquiv p1 p2

proveStructEq : (p1, p2 : Expr) 
            -> Dec (StructEquiv p1 p2)
proveStructEq p1 p2 = 
    case decEq p1 p2 of 
        Yes Refl => Yes (MkStructEquiv Refl)
        No  neq  => No (\(MkStructEquiv Refl) => neq Refl)

data FuncEquiv : (p1, p2 : Expr) -> Type where 
    MkFuncEquiv : StructEquiv p1 p2 -> eval env1 p1 = eval env2 p2 -> FuncEquiv p1 p2
        
proveFuncEq : {env1 : Env}
           -> {env2 : Env}
           -> (p1, p2 : Expr) 
           -> (structEq : StructEquiv p1 p2) 
           -> FuncEquiv p1 p2
proveFuncEq {env1} {env2} p1 p1 (MkStructEquiv Refl) = MkFuncEquiv {env1} (MkStructEquiv Refl) Refl 

-------------------------------------------------------------------

data DeBruijn : (p, d : Expr) -> Type where 
    MkDeBruijn : DeBruijn p (deBruijn 0 p)

data IndexExp : (p : Expr) -> (p' : InExpr) -> Type where 
    MkIndex : IndexExp p (indExp 0 p)

data Proj : (p, d  : Expr) -> (p', d' : InExpr) -> Type where  
    MkProj : DeBruijn p d -> IndexExp p p' -> IndexExp d d' -> p' = d' -> eval v p = convert (inEval env p') -> eval v d = convert (inEval env d') -> Proj p d p' d'  

funEq : (p : Expr) 
     -> (prj: Proj p d p' d')
     -> inEval v p' = inEval v d'
funEq p (MkProj prf1 prf2 prf3 prf4 prf5 prf6) = rewrite prf4 in Refl

-- getRelDe : {p,d : Expr} -> DeBruijn p d -> Expr
-- getRelDe {d=deBruijn 0 p} (MkDeBruijn) = deBruijn 0 p

-- data StructEquivNew : (px, py : Expr) -> Type where 
--    MkStructEquivNew : (d1 = d2) -> DeBruijn px d1 -> DeBruijn py d2 -> Proj px d1 px' p1' -> Proj py d2 py' p2' -> StructEquivNew px py

{-
proveStructEqNew : (p1, p2 : Expr) 
               -> Maybe (StructEquivNew p1 p2)
proveStructEqNew p1 p2 with (MkDeBruijn {p=p1})  
    proveStructEqNew p1 p2 | d1 with (MkDeBruijn {p=p2})  
        proveStructEqNew p1 p2 | d1 |  d2  = 
            case decEq (deBruijn 0 p1) (deBruijn 0 p2) of 
                Yes prf => Just (MkStructEquivNew prf d1 d2)
                No neq => Nothing 

-------------------------------------------------------------------
deLam2 :   {env : Env} 
        -> (v2 : VarName)
        -> (e2 : Expr)
        -> eval env (MkLam v2 e2) = eval env (MkLam 0 (deBruijn 0 (sub [] v2 0 e2))) 
deLam2 {env=MkEnv e} v2 e2 = Refl
    -- deLam2 v2 (MkVar v) | No contra = ?a11


deLam3 : (e : Expr) 
      -> (v : Nat) 
      -> (e2 : Expr)
      ->  eval (MkEnv [(v, eval (MkEnv []) e2)]) e = 
          eval (MkEnv [(0, eval (MkEnv []) (deBruijn 0 e2))]) (deBruijn 0 (sub [] v 0 e)) 
deLam3 (MkVar v1) v (MkVar v2) with (decEq v v1) 
    deLam3 (MkVar v) v (MkVar v2) | Yes Refl = ?t0 
    deLam3 (MkVar v1) v (MkVar v2) | No c    = ?t1
deLam3 _ _ _ = ?t99


deBruijnLem1 : {env : Env} -> (p: Expr) -> DeBruijn p (deBruijn 0 p) -> eval (MkEnv []) p = eval (MkEnv []) (deBruijn 0 p) 
deBruijnLem1 {env} (MkVar v) x = Refl
-- with (assert_total (deBruijnLem1 {env} (MkVar v) x))
  --  deBruijnLem1 {env} (MkVar v) x | hypa = rewrite hypa in Refl
deBruijnLem1 {env} (MkApp (MkLam v e) e2) x with (deLam2 {env} v e)
    deBruijnLem1 {env} (MkApp (MkLam v e) e2) x | Refl with (deBruijnLem1 {env} e2 MkDeBruijn)
    deBruijnLem1 {env} (MkApp (MkLam v e) e2) x  | Refl | prf2 =  ?g0
deBruijnLem1 _ _ = ?never
                                       
-- not used...
evalRefl : (p1 : Expr) 
        -> eval (MkEnv []) p1 = eval (MkEnv []) p1 
evalRefl p1 = Refl


funcEquiv : (p1, p2 : Expr) -> StructEquivNew p1 p2 -> eval (MkEnv []) p1 = eval (MkEnv []) p2
funcEquiv p1 p2 (MkStructEquivNew dEqd (MkDeBruijn {p=p1}) (MkDeBruijn {p=p2})) with (deBruijnLem1 {env=MkEnv []} p1 (MkDeBruijn {p=p1}))
    funcEquiv p1 p2 (MkStructEquivNew dEqd (MkDeBruijn {p=p1}) (MkDeBruijn {p=p2})) | prf with (deBruijnLem1 {env=MkEnv []} p2 (MkDeBruijn {p=p2})) 
        funcEquiv p1 p2 (MkStructEquivNew dEqd (MkDeBruijn {p=p1}) (MkDeBruijn {p=p2})) | prf | prf2 
             = rewrite prf in rewrite prf2 in rewrite dEqd in Refl
-}
