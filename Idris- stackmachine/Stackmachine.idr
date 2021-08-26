module Stackmachine 

import Instruction

Stack : Type
Stack = List Nat

Variable : Type
Variable = Nat 

myAnd : Nat -> Nat -> Nat
myAnd (S (Z)) (S (Z))   = (S (Z))
myAnd (S (Z)) (Z)       = Z
myAnd Z (S (Z))         = Z
myAnd Z Z               = Z

myOr : Nat -> Nat -> Nat
myOr (S (Z)) (S (Z))   = (S (Z))
myOr (S (Z)) (Z)       = (S (Z))
myOr Z (S (Z))         = (S (Z))
myOr Z Z               = Z

isEQ : Nat -> Nat -> Nat
isEQ a b = case decEq a b of
    Yes Refl =>  (S (Z))
    No contra => Z

isGT : Nat -> Nat -> Nat
isGT a b = case isLTE (S b) a of
    Yes p =>  (S (Z))
    No contra => Z

isGE : Nat -> Nat -> Nat
isGE a b = case isLTE b a of
    Yes p =>  (S (Z))
    No contra => Z

replace : Nat -> Nat -> Stack -> Stack
replace pos newVal list = (take pos list) ++ (newVal :: (drop (S pos) list))

decode' : List Instruction -> List Instruction -> List Variable -> Stack -> (Stack, List Variable)
decode' o [] v s = (s,v)
decode' o (LABEL n :: is) v s = decode' o is v s
decode' o (PUSH i :: is) v s = decode' o is v (i :: s)
decode' o (ADD :: is) v (n:: (m :: s )) = decode' o is v (m+n :: s)
decode' o (SUB :: is) v (n:: (m :: s )) = 
    case isLTE n m of
        Yes p => decode' o is v (m-n :: s)
        No  c => (s,v)
decode' o (MUL :: is) v (n :: (m :: s)) = decode' o is v (m*n :: s)
decode' o (DIV :: is) v (n :: (m :: s)) = decode' o is v (div m n  :: s)
decode' o (AND :: is) v (n :: (m :: s)) = decode' o is v ((m `myAnd` n) :: s)
decode' o (OR :: is)  v (n :: (m :: s)) = decode' o is v ((m `myOr` n) :: s)
decode' o (ISEQ :: is) v (n :: (m :: s)) = decode' o is v ((m `isEQ` n) :: s)
decode' o (ISGT :: is) v (n :: (m :: s)) = decode' o is v ((m `isGT` n) :: s) 
decode' o (ISGE :: is) v (n :: (m :: s)) = decode' o is v ((m `isGE` n) :: s)
decode' o (JMP n :: is) v s = decode' o (dropWhile (\arg => not (decAsBool (decEq (LABEL n) arg))) o) v s
decode' o (LOAD n :: is) v s = 
    case inBounds n v of 
        Yes p => decode' o is v ((index n v) :: s)
        No c => (s,v)
decode' o (STORE n :: is) v (sh :: s) = decode' o is (replace n sh v) s
decode' o (NOT :: is) v ((S Z) :: s) = decode' o is v (Z :: s)
decode' o (NOT :: is) v (Z :: s) = decode' o is v (S Z :: s)

decode : List Instruction -> (Stack, List Variable)
decode is = decode' is is [] []

example : List Instruction
example = [
           PUSH 6, 
           STORE 0, 
           PUSH 4, 
           STORE 1, 
           LOAD 0, 
           LOAD 1, 
           ISGT, 
           JIF "BOB", 
           LOAD 1, 
           STORE 2, 
           JMP "END",
           LABEL "BOB" ,
           LOAD 0, 
           STORE 2, 
           LABEL "END",
           HALT
          ]

example2 : List Instruction
example2 = [
            PUSH 6,
            STORE 0,
            PUSH 4,
            STORE 1,
            PUSH 0,
            STORE 2,
            LABEL "START",
            LOAD 1,
            PUSH 1,
            ISGE,
            NOT,
            JIF "DONE",
            LOAD 0,
            LOAD 2,
            ADD,
            STORE 2,
            LOAD 1,
            PUSH 1,
            SUB,
            STORE 1,
            JMP "START",
            LABEL "DONE"
             ]