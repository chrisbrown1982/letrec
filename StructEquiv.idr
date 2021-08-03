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
    