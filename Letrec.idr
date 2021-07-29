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

maximum : List Nat -> Nat 
maximum []  = Z
maximum [x] = x 
maximum (x::x'::xs) = assert_total (maximum ((if x >= x' then x else x')::xs))

mapXtoZ : (x_i : Nat) 
       -> (xInFVLet : Bool)
       -> (fvN : List Nat)
       -> (z_i : Nat)
       -> Nat    
mapXtoZ x_i xInFVLet fvN z_i =
    case ((not xInFVLet) || (not (elem x_i fvN))) of
       True  => x_i  
       False => z_i 

mutual 
    subsLetD : (x_i : Nat)
            -> (z_i : Nat)
            -> (d : LetrecD)
            -> LetrecD 
    subsLetD x_i z_i MkEmpty = MkEmpty 
    subsLetD x_i z_i (MkBind d e) = MkBind z_i (subE e x_i (MkVal (MkVar z_i)))
    subsLetD x_i z_i (MkSeqB d1 d2) = MkSeqB (subsLetD x_i z_i d1) (subsLetD x_i z_i d2)

    subsLetDs : (x_i : Nat)
           -> (z_i : Nat)
           -> (ds : List LetrecD)
           -> List LetrecD
    subsLetDs x_i z_i [] = []
    subsLetDs x_i z_i (MkEmpty :: ds) = MkEmpty :: (subsLetDs x_i z_i ds)
    subsLetDs x_i z_i (MkBind d e :: ds) = MkBind z_i (subE e x_i (MkVal (MkVar z_i))) :: (subsLetDs x_i z_i ds) 
    subsLetDs x_i z_i (MkSeqB d1 d2 :: ds) = MkSeqB (subsLetD x_i z_i d1) (subsLetD x_i z_i d2) :: (subsLetDs x_i z_i ds)  

    ||| Capture Avoiding Substitution 
    ||| E[x:=E_1] stands for a capture avoiding subbstitution of E_1
    ||| for each free occurrence of x in E
    subE : (e : LetrecE) -> (x : Nat) -> (e1 : LetrecE) -> LetrecE
    -- x[x:=N] = N
    -- x[x:=N] = y; y != x
    subE (MkVal (MkVar n)) x eS = 
        case decEq n x of 
            Yes Refl => eS
            No  c    => (MkVal (MkVar n))

    -- (E_1 E_2)[x:=N] = E_1[x:=N]E_2[x:=N]
    subE (MkAppE e1 e2) x eS = 
        case subE e1 x eS of 
            e1' => 
                case subE e2 x eS of 
                  e2' => MkAppE e1' e2' 

    -- (\x.E)[x:=N] = \x.E
    -- (\y.E)[x:=N] (y != x) = \z.E[y:=z][x:=N] 
    -- where 
    --    y = z if x !in FV(E) OR y !in FV(N), otherwise z is a fresh variable
    -- I personally find this a bit confusing. 
    -- Thompson's text (Page 29) has a more precise definition:
    -- if e = \x.g then e[f/x] = e
    -- if y is a variable distinct from x, and e = \y.g then 
    --   - if y does not appear free in f, e[f/x] = \y.g[f/x] 
    --   - if y does appear free in f, 
    --        e[f/x] = \z.(g[z/y][f/x])
    --     where z is a variable which does not appear in f or g. (Note that 
    --      have an infinite collection of variables, so that we can always find such
    --      a z.)
    subE (MkVal (MkAbs n e)) x eS =
        case decEq n x of 
            Yes Refl => MkVal (MkAbs n e)
            No  c    =>
                case elem n (fv eS) of 
                    False => MkVal (MkAbs n (subE e x eS))
                    True => 
                        let eS' = maximum (fv eS)
                            e'  = maximum (fv e)
                            z   = (S ( plus eS' e' ))
                            z'  = MkVal (MkVar z)
                        in  MkVal (MkAbs z (assert_total (subE (assert_total (subE e n z')) x eS)))
            
    subE (MkLetRec d e) x eS = ?hole
    
