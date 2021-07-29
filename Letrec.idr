module Letrec

import Decidable.Equality

%default total

mutual 
    data LetrecD : Type where 
        MkEmpty : LetrecD 
        MkBind  : (x : Nat) -> (e : LetrecE) -> LetrecD
        MkSeqB  : (d1 : LetrecD) -> (d2 : LetrecD) -> LetrecD

    data LetrecE : Type where 
        MkVal    : (v : LetrecV) -> LetrecE 
        MkAppE   : (e1 : LetrecE) -> (e2 : LetrecE) -> LetrecE
        MkLetRec : (d : LetrecD) -> (e : LetrecE) -> LetrecE


    data LetrecV : Type where 
        MkVar : (n : Nat) -> LetrecV 
        MkAbs : (n : Nat) -> (e : LetrecE) -> LetrecV

||| lMinus l x = l - x 
lMinus : (l : List Nat) -> (x : Nat) -> List Nat 
lMinus [] x = []
lMinus (y::ys) x = 
    case decEq y x of 
        Yes Refl => lMinus ys x
        No  c    => y :: (lMinus ys x)


mutual 
    fvD : (d : LetrecD) -> List Nat 
    fvD (MkEmpty) = []
    fvD (MkBind x e) = lMinus (fv e) x 
    fvD (MkSeqB d1 rest) = fvD d1 ++ fvD rest 

    fv : (e : LetrecE) -> List Nat
    fv (MkVal (MkVar n)) = [n]
    fv (MkVal (MkAbs x e)) = lMinus (fv e) x
    fv (MkAppE e1 e2) = (fv e1) ++ (fv e2)
    fv (MkLetRec d e) = fvD d ++ fv e

||| Capture Avoiding Substitution 
||| E[x:=E_1] stands for a capture avoiding subbstitution of E_1
||| for each free occurrence of x in E
subE : (e : LetrecE) -> (x : Nat) -> (e1 : LetrecE) -> LetrecE
subE (MkVal (MkVar n)) x eS      = 
    case decEq n x of 
        Yes Refl => eS
        No  c    => (MkVal (MkVar n))
subE (MkVal (MkAbs n e)) x eS    = ?hx



subE (MkAppE e1 e2) x eS = 
    case subE e1 x eS of 
        e1' => 
          case subE e2 x eS of 
            e2' => MkAppE e1' e2' 
subE (MkLetRec d e) x eS = ?h22
