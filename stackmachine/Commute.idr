module Commute

import Lang
import StackMachine
import Correctness

%access public export
%default total


evalPlusCommutative : (e1, e2 : Expr) -> eval (Plus e1 e2) = eval (Plus e2 e1)
evalPlusCommutative (Plus e1 e2) (Plus e3 e4) with (eval e1)
    evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa with (eval e2)
        evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa | hypb with (eval e3)
            evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa | hypb | hypc with (eval e4)
                evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa | hypb | hypc | hypd = 
                    rewrite plusCommutative (plus hypa hypb) (plus hypc hypd) in Refl

evalPlusCommutative (Mult e1 e2) (Plus e3 e4) with (eval e1)
    evalPlusCommutative (Mult e1 e2) (Plus e3 e4) | hypa with (eval e2)
        evalPlusCommutative (Mult e1 e2) (Plus e3 e4) | hypa | hypb with (eval e3)
            evalPlusCommutative (Mult e1 e2) (Plus e3 e4) | hypa | hypb | hypc with (eval e4)
                evalPlusCommutative (Mult e1 e2) (Plus e3 e4) | hypa | hypb | hypc | hypd = 
                    rewrite plusCommutative (mult hypa hypb) (plus hypc hypd) in Refl 

evalPlusCommutative (Plus e1 e2) (Mult e3 e4) with (eval e1)
    evalPlusCommutative (Plus e1 e2) (Mult e3 e4) | hypa with (eval e2)
        evalPlusCommutative (Plus e1 e2) (Mult e3 e4) | hypa | hypb with (eval e3)
            evalPlusCommutative (Plus e1 e2) (Mult e3 e4) | hypa | hypb | hypc with (eval e4)
                evalPlusCommutative (Plus e1 e2) (Mult e3 e4) | hypa | hypb | hypc | hypd = 
                    rewrite plusCommutative (plus hypa hypb) (mult hypc hypd) in Refl 

evalPlusCommutative (Mult e1 e2) (Mult e3 e4) with (eval e1)
    evalPlusCommutative (Mult e1 e2) (Mult e3 e4) | hypa with (eval e2)
        evalPlusCommutative (Mult e1 e2) (Mult e3 e4) | hypa | hypb with (eval e3)
            evalPlusCommutative (Mult e1 e2) (Mult e3 e4) | hypa | hypb | hypc with (eval e4)
                evalPlusCommutative (Mult e1 e2) (Mult e3 e4) | hypa | hypb | hypc | hypd = 
                    rewrite plusCommutative (mult hypa hypb) (mult hypc hypd) in Refl 

evalPlusCommutative (Plus e1 e2) (Const n) with (eval e1)
    evalPlusCommutative (Plus e1 e2) (Const n) | hypa with (eval e2)
        evalPlusCommutative (Plus e1 e2) (Const n) | hypa | hypb = 
            rewrite plusCommutative (plus hypa hypb) n in Refl

evalPlusCommutative (Mult e1 e2) (Const n) with (eval e1)
    evalPlusCommutative (Mult e1 e2) (Const n) | hypa with (eval e2)
        evalPlusCommutative (Mult e1 e2) (Const n) | hypa | hypb = 
            rewrite plusCommutative (mult hypa hypb) n in Refl

evalPlusCommutative (Const n) (Plus e3 e4) with (eval e3) 
    evalPlusCommutative (Const n) (Plus e3 e4) | hypa with (eval e4) 
        evalPlusCommutative (Const n) (Plus e3 e4) | hypa | hypb = 
            rewrite plusCommutative n (plus hypa hypb) in Refl

evalPlusCommutative (Const n) (Mult e3 e4) with (eval e3) 
    evalPlusCommutative (Const n) (Mult e3 e4) | hypa with (eval e4) 
        evalPlusCommutative (Const n) (Mult e3 e4) | hypa | hypb = 
            rewrite plusCommutative n (mult hypa hypb) in Refl

evalPlusCommutative (Const n1) (Const n2) = 
    rewrite plusCommutative n1 n2 in Refl



execCommute : (i, j : Nat)
           -> (s : Stack) 
           -> exec Add (i::j::s) = exec Add (j::i::s)
execCommute i j s = rewrite plusCommutative i j in Refl


addPushCom : (n1 : Nat)
          -> (s : Stack)
          -> (e1, e2 : Expr)
          -> run ((comp e1 ++ comp e2 ++ [Add]) ++ [Add]) (n1 :: s) 
           = run ((comp e1 ++ comp e2 ++ [Add]) ++ [Push n1, Add]) s
addPushCom n1 s e1 e2 with (runPartial (comp e1 ++ comp e2 ++ [Add]) [Push n1, Add] s)
    addPushCom n1 s e1 e2 | hypa =
        rewrite hypa in 
            rewrite runa e1 e2 s in 
                rewrite runb e1 e2 s in 
                    rewrite (cmpCorrectStack e1 s) in 
                        rewrite (cmpCorrectStack e2 $ [eval e1] ++ s) in 
                            rewrite (runPartial (comp e1 ++ comp e2 ++ [Add]) [Add] (n1::s)) in
                                rewrite (runa e1 e2 (n1::s)) in
                                    rewrite (runb e1 e2 (n1::s)) in 
                                        rewrite cmpCorrectStack e1 (n1::s) in 
                                            rewrite cmpCorrectStack e2 $ [eval e1] ++ (n1::s) in 
                                                rewrite plusCommutative n1 (plus (eval e1) (eval e2)) in 
                                                    Refl 

mulPushCom : (n1 : Nat)
         -> (s : Stack)
         -> (e1, e2 : Expr)
         -> run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Add]) (n1 :: s) 
            = run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Push n1, Add]) s
mulPushCom n1 s e1 e2 with (runPartial (comp e1 ++ comp e2 ++ [Mul]) [Push n1, Add] s)
    addPushCom n1 s e1 e2 | hypa 
    =  rewrite hypa in 
            rewrite runMa e1 e2 s in 
                rewrite runMb e1 e2 s in 
                    rewrite (cmpCorrectStack e1 s) in 
                        rewrite (cmpCorrectStack e2 $ [eval e1] ++ s) in
                          rewrite (runPartial (comp e1 ++ comp e2 ++ [Mul]) [Add] (n1::s)) in
                                rewrite (runMa e1 e2 (n1::s)) in
                                    rewrite (runMb e1 e2 (n1::s)) in 
                                        rewrite cmpCorrectStack e1 (n1::s) in 
                                            rewrite cmpCorrectStack e2 $ [eval e1] ++ (n1::s) in
                                               rewrite plusCommutative n1 (mult (eval e1) (eval e2)) in 
                                                  Refl

addPushCom2 : (n2 : Nat)
          ->  (s : Stack)
          ->  (e1, e2 : Expr)
          ->  run ((comp e1 ++ comp e2 ++ [Add]) ++ [Push n2, Add]) s = 
              run ((comp e1 ++ comp e2 ++ [Add]) ++ [Add]) (n2 :: s)
addPushCom2 n2 s e1 e2 =
    rewrite addPushCom n2 s e1 e2 in Refl

mulPushCom2 : (n2 : Nat)
    ->  (s : Stack)
    ->  (e1, e2 : Expr)
    ->  run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Push n2, Add]) s = 
        run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Add]) (n2 :: s)
mulPushCom2 n2 s e1 e2 =
    rewrite mulPushCom n2 s e1 e2 in Refl

addPushCom3 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )
           -> run ((comp e1 ++ comp e2 ++ [Add]) ++ (comp e3 ++ comp e4 ++ [Add]) ++ [Add]) s =
              run ((comp e3 ++ comp e4 ++ [Add]) ++ (comp e1 ++ comp e2 ++ [Add]) ++ [Add]) s
addPushCom3 e1 e2 e3 e4 s = 
    rewrite runPartial (comp e1 ++ comp e2 ++ [Add])  ((comp e3 ++ comp e4 ++ [Add]) ++ [Add]) s in 
      rewrite runa e1 e2 s in
        rewrite runb e1 e2 s in 
          rewrite runPartial (comp e3 ++ comp e4 ++ [Add])  [Add] (exec Add (run (comp e2) (run (comp e1) s))) in 
            rewrite runa e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
              rewrite runb e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
                rewrite cmpCorrectStack e1 s in 
                  rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
                    rewrite cmpCorrectStack e3 (plus (eval e1) (eval e2) :: s) in 
                      rewrite cmpCorrectStack e4 (eval e3 :: plus (eval e1) (eval e2) :: s) in 
                        rewrite runPartial (comp e3 ++ comp e4 ++ [Add])  ((comp e1 ++ comp e2 ++ [Add]) ++ [Add]) s in 
                          rewrite runa e3 e4 s in 
                            rewrite runb e3 e4 s in 
                              rewrite runPartial (comp e1 ++ comp e2 ++ [Add])  [Add] (exec Add (run (comp e4) (run (comp e3) s))) in 
                                rewrite runa e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in 
                                  rewrite runb e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in
                                    rewrite cmpCorrectStack e3 s in
                                      rewrite cmpCorrectStack e4 (eval e3 :: s) in
                                        rewrite cmpCorrectStack e1 (plus (eval e3) (eval e4) :: s) in
                                          rewrite cmpCorrectStack e2 (eval e1 :: plus (eval e3) (eval e4) :: s) in
                                            rewrite plusCommutative (plus (eval e1) (eval e2)) (plus (eval e3) (eval e4)) in Refl


mulPushCom3 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )
           -> run ((comp e1 ++ comp e2 ++ [Add]) ++ (comp e3 ++ comp e4 ++ [Mul]) ++ [Add]) s =
              run ((comp e3 ++ comp e4 ++ [Mul]) ++ (comp e1 ++ comp e2 ++ [Add]) ++ [Add]) s
mulPushCom3 e1 e2 e3 e4 s = 
 rewrite runPartial (comp e1 ++ comp e2 ++ [Add])  ((comp e3 ++ comp e4 ++ [Mul]) ++ [Add]) s in 
   rewrite runa e1 e2 s in
     rewrite runb e1 e2 s in 
       rewrite runPartial (comp e3 ++ comp e4 ++ [Mul]) [Add] (exec Add (run (comp e2) (run (comp e1) s))) in 
         rewrite runMa e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
           rewrite runMb e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
             rewrite cmpCorrectStack e1 s in 
               rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
                 rewrite cmpCorrectStack e3 (plus (eval e1) (eval e2) :: s) in 
                   rewrite cmpCorrectStack e4 (eval e3 :: plus (eval e1) (eval e2) :: s) in 
                     rewrite runPartial (comp e3 ++ comp e4 ++ [Mul])  ((comp e1 ++ comp e2 ++ [Add]) ++ [Add]) s in
                       rewrite runMa e3 e4 s in 
                        rewrite runMb e3 e4 s in 
                         rewrite runPartial (comp e1 ++ comp e2 ++ [Add])  [Add] (exec Mul (run (comp e4) (run (comp e3) s))) in
                           rewrite runa e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                             rewrite runb e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                               rewrite cmpCorrectStack e3 s in
                                 rewrite cmpCorrectStack e4 (eval e3 :: s) in
                                  rewrite cmpCorrectStack e1 (mult (eval e3) (eval e4) :: s) in
                                    rewrite cmpCorrectStack e2 (eval e1 :: mult (eval e3) (eval e4) :: s) in
                                     rewrite plusCommutative (plus (eval e1) (eval e2)) (mult (eval e3) (eval e4)) in Refl 

mulPushCom4 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )
           -> run ((comp e1 ++ comp e2 ++ [Mul]) ++ (comp e3 ++ comp e4 ++ [Add]) ++ [Add]) s =
              run ((comp e3 ++ comp e4 ++ [Add]) ++ (comp e1 ++ comp e2 ++ [Mul]) ++ [Add]) s
mulPushCom4 e1 e2 e3 e4 s = 
    rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) ((comp e3 ++ comp e4 ++ [Add]) ++ [Add]) s in 
      rewrite runMa e1 e2 s in
        rewrite runMb e1 e2 s in 
          rewrite runPartial (comp e3 ++ comp e4 ++ [Add]) [Add] (exec Mul (run (comp e2) (run (comp e1) s))) in 
            rewrite runa e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
              rewrite runb e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
                rewrite cmpCorrectStack e1 s in 
                   rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
                     rewrite cmpCorrectStack e3 (mult (eval e1) (eval e2) :: s) in 
                       rewrite cmpCorrectStack e4 (eval e3 :: mult (eval e1) (eval e2) :: s) in 
                         rewrite runPartial (comp e3 ++ comp e4 ++ [Add])  ((comp e1 ++ comp e2 ++ [Mul]) ++ [Add]) s in
                           rewrite runa e3 e4 s in 
                            rewrite runb e3 e4 s in 
                              rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) [Add] (exec Add (run (comp e4) (run (comp e3) s))) in
                               rewrite runMa e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in 
                                 rewrite runMb e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in 
                                  rewrite cmpCorrectStack e3 s in
                                    rewrite cmpCorrectStack e4 (eval e3 :: s) in
                                     rewrite cmpCorrectStack e1 (plus (eval e3) (eval e4) :: s) in
                                      rewrite cmpCorrectStack e2 (eval e1 :: plus (eval e3) (eval e4) :: s) in
                                        rewrite plusCommutative (mult (eval e1) (eval e2)) (plus (eval e3) (eval e4)) in Refl 
              
mulPushCom5 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )
           -> run ((comp e1 ++ comp e2 ++ [Mul]) ++ (comp e3 ++ comp e4 ++ [Mul]) ++ [Add]) s =
              run ((comp e3 ++ comp e4 ++ [Mul]) ++ (comp e1 ++ comp e2 ++ [Mul]) ++ [Add]) s
mulPushCom5 e1 e2 e3 e4 s = 
    rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) ((comp e3 ++ comp e4 ++ [Mul]) ++ [Add]) s in 
        rewrite runMa e1 e2 s in
          rewrite runMb e1 e2 s in 
            rewrite runPartial (comp e3 ++ comp e4 ++ [Mul]) [Add] (exec Mul (run (comp e2) (run (comp e1) s))) in 
              rewrite runMa e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
                rewrite runMb e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
                  rewrite cmpCorrectStack e1 s in 
                     rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
                       rewrite cmpCorrectStack e3 (mult (eval e1) (eval e2) :: s) in 
                         rewrite cmpCorrectStack e4 (eval e3 :: mult (eval e1) (eval e2) :: s) in 
                           rewrite runPartial (comp e3 ++ comp e4 ++ [Mul]) ((comp e1 ++ comp e2 ++ [Mul]) ++ [Add]) s in
                             rewrite runMa e3 e4 s in 
                              rewrite runMb e3 e4 s in 
                                rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) [Add] (exec Mul (run (comp e4) (run (comp e3) s))) in
                                 rewrite runMa e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                                   rewrite runMb e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                                    rewrite cmpCorrectStack e3 s in
                                      rewrite cmpCorrectStack e4 (eval e3 :: s) in
                                       rewrite cmpCorrectStack e1 (mult (eval e3) (eval e4) :: s) in
                                        rewrite cmpCorrectStack e2 (eval e1 :: mult (eval e3) (eval e4) :: s) in
                                          rewrite plusCommutative (mult (eval e1) (eval e2)) (mult (eval e3) (eval e4)) in Refl 

cmpPlusCommutative : (e1, e2 : Expr) 
                  -> (s : Stack )
                  -> run (comp (Plus e1 e2)) s = run (comp (Plus e2 e1)) s
cmpPlusCommutative (Const n1) (Const n2) s = rewrite plusCommutative n1 n2 in Refl 

cmpPlusCommutative (Const n1) (Plus e1 e2) s with (addPushCom n1 s e1 e2)
    cmpPlusCommutative (Const n1) (Plus e1 e2) s | hypa = rewrite hypa in Refl

cmpPlusCommutative (Const n1) (Mult e1 e2) s with (mulPushCom n1 s e1 e2)
    cmpPlusCommutative (Const n1) (Mult e1 e2) s | hypa = rewrite hypa in Refl

cmpPlusCommutative (Plus e1 e2) (Const n2) s with (addPushCom2 n2 s e1 e2)
    cmpPlusCommutative (Plus e1 e2) (Const n2) s | hypa = rewrite hypa in Refl 

cmpPlusCommutative (Mult e1 e2) (Const n2) s with (mulPushCom2 n2 s e1 e2)
    cmpPlusCommutative (Mult e1 e2) (Const n2) s | hypa = rewrite hypa in Refl

cmpPlusCommutative (Plus e1 e2) (Plus e3 e4 ) s with (addPushCom3 e1 e2 e3 e4 s)
    cmpPlusCommutative (Plus e1 e2) (Plus e3 e4 ) s | hypa = rewrite hypa in Refl 

cmpPlusCommutative (Mult e1 e2) (Mult e3 e4) s with (mulPushCom5 e1 e2 e3 e4 s)
    cmpPlusCommutative (Mult e1 e2) (Mult e3 e4) s | hypa = rewrite hypa in Refl

cmpPlusCommutative (Plus e1 e2) (Mult e3 e4) s with (mulPushCom3 e1 e2 e3 e4 s) 
    cmpPlusCommutative (Plus e1 e2) (Mult e3 e4) s | hypa = rewrite hypa in Refl 

cmpPlusCommutative (Mult e1 e2) (Plus e3 e4) s with (mulPushCom4 e1 e2 e3 e4 s)
    cmpPlusCommutative (Mult e1 e2) (Plus e3 e4) s | hypa = rewrite hypa in Refl


--------------------------------------------------------------
mulPushCom0 : (n1 : Nat)
          -> (s : Stack)
          -> (e1, e2 : Expr)
          -> run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Mul]) (n1 :: s) 
           = run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Push n1, Mul]) s
mulPushCom0 n1 s e1 e2 with (runPartial (comp e1 ++ comp e2 ++ [Mul]) [Push n1, Mul] s)
    mulPushCom0 n1 s e1 e2 | hypa =
        rewrite hypa in 
            rewrite runMa e1 e2 s in 
                rewrite runMb e1 e2 s in 
                    rewrite (cmpCorrectStack e1 s) in 
                        rewrite (cmpCorrectStack e2 $ [eval e1] ++ s) in 
                            rewrite (runPartial (comp e1 ++ comp e2 ++ [Mul]) [Mul] (n1::s)) in
                                rewrite (runMa e1 e2 (n1::s)) in
                                    rewrite (runMb e1 e2 (n1::s)) in 
                                        rewrite cmpCorrectStack e1 (n1::s) in 
                                            rewrite cmpCorrectStack e2 $ [eval e1] ++ (n1::s) in 
                                                rewrite multCommutative n1 (mult (eval e1) (eval e2)) in 
                                                    Refl 


mulPushComL : (n1 : Nat)
         -> (s : Stack)
         -> (e1, e2 : Expr)
         -> run ((comp e1 ++ comp e2 ++ [Add]) ++ [Mul]) (n1 :: s) 
            = run ((comp e1 ++ comp e2 ++ [Add]) ++ [Push n1, Mul]) s
mulPushComL n1 s e1 e2 with (runPartial (comp e1 ++ comp e2 ++ [Add]) [Push n1, Mul] s)
    addPushCom n1 s e1 e2 | hypa 
    =  rewrite hypa in 
            rewrite runa e1 e2 s in 
                rewrite runb e1 e2 s in 
                    rewrite (cmpCorrectStack e1 s) in 
                        rewrite (cmpCorrectStack e2 $ [eval e1] ++ s) in
                          rewrite (runPartial (comp e1 ++ comp e2 ++ [Add]) [Mul] (n1::s)) in
                                rewrite (runa e1 e2 (n1::s)) in
                                    rewrite (runb e1 e2 (n1::s)) in 
                                        rewrite cmpCorrectStack e1 (n1::s) in 
                                            rewrite cmpCorrectStack e2 $ [eval e1] ++ (n1::s) in
                                               rewrite multCommutative n1 (plus (eval e1) (eval e2)) in 
                                                  Refl

mulPushComL2 : (n1 : Nat)
           -> (s : Stack)
           -> (e1, e2 : Expr)
           -> run ((comp e1 ++ comp e2 ++ [Add]) ++ [Push n1, Mul]) s = run ((comp e1 ++ comp e2 ++ [Add]) ++ [Mul]) (n1 :: s)
mulPushComL2 n1 s e1 e2 = rewrite mulPushComL n1 s e1 e2 in Refl

mulPushComL3 : (n2 : Nat) 
             -> (s : Stack) 
             -> (e1, e2 : Expr)
             -> run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Push n2, Mul]) s = run ((comp e1 ++ comp e2 ++ [Mul]) ++ [Mul]) (n2 :: s)
mulPushComL3 n2 s e1 e2 = rewrite mulPushCom0 n2 s e1 e2 in Refl

mulPushCom6 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )
           -> run ((comp e1 ++ comp e2 ++ [Add]) ++ (comp e3 ++ comp e4 ++ [Mul]) ++ [Mul]) s =
              run ((comp e3 ++ comp e4 ++ [Mul]) ++ (comp e1 ++ comp e2 ++ [Add]) ++ [Mul]) s
mulPushCom6 e1 e2 e3 e4 s = 
    rewrite runPartial (comp e1 ++ comp e2 ++ [Add]) ((comp e3 ++ comp e4 ++ [Mul]) ++ [Mul]) s in 
        rewrite runa e1 e2 s in
          rewrite runb e1 e2 s in 
            rewrite runPartial (comp e3 ++ comp e4 ++ [Mul]) [Mul] (exec Add (run (comp e2) (run (comp e1) s))) in 
              rewrite runMa e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
                rewrite runMb e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
                  rewrite cmpCorrectStack e1 s in 
                     rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
                       rewrite cmpCorrectStack e3 (plus (eval e1) (eval e2) :: s) in 
                         rewrite cmpCorrectStack e4 (eval e3 :: plus (eval e1) (eval e2) :: s) in 
                           rewrite runPartial (comp e3 ++ comp e4 ++ [Mul]) ((comp e1 ++ comp e2 ++ [Add]) ++ [Mul]) s in
                             rewrite runMa e3 e4 s in 
                              rewrite runMb e3 e4 s in 
                                rewrite runPartial (comp e1 ++ comp e2 ++ [Add]) [Mul] (exec Mul (run (comp e4) (run (comp e3) s))) in
                                 rewrite runa e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                                   rewrite runb e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                                    rewrite cmpCorrectStack e3 s in
                                      rewrite cmpCorrectStack e4 (eval e3 :: s) in
                                       rewrite cmpCorrectStack e1 (mult (eval e3) (eval e4) :: s) in
                                        rewrite cmpCorrectStack e2 (eval e1 :: mult (eval e3) (eval e4) :: s) in
                                         rewrite multCommutative (plus (eval e1) (eval e2)) (mult (eval e3) (eval e4)) in Refl

mulPushCom7 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )
           -> run ((comp e1 ++ comp e2 ++ [Add]) ++ (comp e3 ++ comp e4 ++ [Add]) ++ [Mul]) s =
              run ((comp e3 ++ comp e4 ++ [Add]) ++ (comp e1 ++ comp e2 ++ [Add]) ++ [Mul]) s
mulPushCom7 e1 e2 e3 e4 s = 
    rewrite runPartial (comp e1 ++ comp e2 ++ [Add]) ((comp e3 ++ comp e4 ++ [Add]) ++ [Mul]) s in 
        rewrite runa e1 e2 s in
          rewrite runb e1 e2 s in 
            rewrite runPartial (comp e3 ++ comp e4 ++ [Add]) [Mul] (exec Add (run (comp e2) (run (comp e1) s))) in 
              rewrite runa e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
                rewrite runb e3 e4 (exec Add (run (comp e2) (run (comp e1) s))) in 
                  rewrite cmpCorrectStack e1 s in 
                     rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
                       rewrite cmpCorrectStack e3 (plus (eval e1) (eval e2) :: s) in 
                         rewrite cmpCorrectStack e4 (eval e3 :: plus (eval e1) (eval e2) :: s) in 
                           rewrite runPartial (comp e3 ++ comp e4 ++ [Add]) ((comp e1 ++ comp e2 ++ [Add]) ++ [Mul]) s in
                             rewrite runa e3 e4 s in 
                              rewrite runb e3 e4 s in 
                                rewrite runPartial (comp e1 ++ comp e2 ++ [Add]) [Mul] (exec Add (run (comp e4) (run (comp e3) s))) in
                                 rewrite runa e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in 
                                   rewrite runb e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in 
                                    rewrite cmpCorrectStack e3 s in
                                      rewrite cmpCorrectStack e4 (eval e3 :: s) in
                                       rewrite cmpCorrectStack e1 (plus (eval e3) (eval e4) :: s) in
                                        rewrite cmpCorrectStack e2 (eval e1 :: plus (eval e3) (eval e4) :: s) in
                                         rewrite multCommutative (plus (eval e1) (eval e2)) (plus (eval e3) (eval e4)) in Refl

mulPushCom8 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )                                         
           -> run ((comp e1 ++ comp e2 ++ [Mul]) ++ (comp e3 ++ comp e4 ++ [Mul]) ++ [Mul]) s =
              run ((comp e3 ++ comp e4 ++ [Mul]) ++ (comp e1 ++ comp e2 ++ [Mul]) ++ [Mul]) s
mulPushCom8 e1 e2 e3 e4 s = 
 rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) ((comp e3 ++ comp e4 ++ [Mul]) ++ [Mul]) s in 
  rewrite runMa e1 e2 s in
   rewrite runMb e1 e2 s in 
    rewrite runPartial (comp e3 ++ comp e4 ++ [Mul]) [Mul] (exec Mul (run (comp e2) (run (comp e1) s))) in 
     rewrite runMa e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
      rewrite runMb e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
       rewrite cmpCorrectStack e1 s in 
        rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
         rewrite cmpCorrectStack e3 (mult (eval e1) (eval e2) :: s) in 
          rewrite cmpCorrectStack e4 (eval e3 :: mult (eval e1) (eval e2) :: s) in 
           rewrite runPartial (comp e3 ++ comp e4 ++ [Mul]) ((comp e1 ++ comp e2 ++ [Mul]) ++ [Mul]) s in
            rewrite runMa e3 e4 s in 
             rewrite runMb e3 e4 s in 
              rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) [Mul] (exec Mul (run (comp e4) (run (comp e3) s))) in
               rewrite runMa e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                rewrite runMb e1 e2 (exec Mul (run (comp e4) (run (comp e3) s))) in 
                 rewrite cmpCorrectStack e3 s in
                  rewrite cmpCorrectStack e4 (eval e3 :: s) in
                   rewrite cmpCorrectStack e1 (mult (eval e3) (eval e4) :: s) in
                    rewrite cmpCorrectStack e2 (eval e1 :: mult (eval e3) (eval e4) :: s) in
                     rewrite multCommutative (mult (eval e1) (eval e2)) (mult (eval e3) (eval e4)) in Refl

mulPushCom9 : (e1, e2, e3, e4 : Expr)
           -> (s : Stack )
           -> run ((comp e1 ++ comp e2 ++ [Mul]) ++ (comp e3 ++ comp e4 ++ [Add]) ++ [Mul]) s =
              run ((comp e3 ++ comp e4 ++ [Add]) ++ (comp e1 ++ comp e2 ++ [Mul]) ++ [Mul]) s
mulPushCom9 e1 e2 e3 e4 s = 
    rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) ((comp e3 ++ comp e4 ++ [Add]) ++ [Mul]) s in 
        rewrite runMa e1 e2 s in
         rewrite runMb e1 e2 s in 
          rewrite runPartial (comp e3 ++ comp e4 ++ [Add]) [Mul] (exec Mul (run (comp e2) (run (comp e1) s))) in 
           rewrite runa e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
            rewrite runb e3 e4 (exec Mul (run (comp e2) (run (comp e1) s))) in 
             rewrite cmpCorrectStack e1 s in 
              rewrite cmpCorrectStack e2 $ [eval e1] ++ s in 
               rewrite cmpCorrectStack e3 (mult (eval e1) (eval e2) :: s) in 
                rewrite cmpCorrectStack e4 (eval e3 :: mult (eval e1) (eval e2) :: s) in 
                 rewrite runPartial (comp e3 ++ comp e4 ++ [Add]) ((comp e1 ++ comp e2 ++ [Mul]) ++ [Mul]) s in
                  rewrite runa e3 e4 s in 
                   rewrite runb e3 e4 s in 
                    rewrite runPartial (comp e1 ++ comp e2 ++ [Mul]) [Mul] (exec Add (run (comp e4) (run (comp e3) s))) in
                     rewrite runMa e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in 
                      rewrite runMb e1 e2 (exec Add (run (comp e4) (run (comp e3) s))) in 
                       rewrite cmpCorrectStack e3 s in
                        rewrite cmpCorrectStack e4 (eval e3 :: s) in
                         rewrite cmpCorrectStack e1 (plus (eval e3) (eval e4) :: s) in
                          rewrite cmpCorrectStack e2 (eval e1 :: plus (eval e3) (eval e4) :: s) in
                           rewrite multCommutative (mult (eval e1) (eval e2)) (plus (eval e3) (eval e4)) in Refl

cmpMultCommutative : (e1, e2 : Expr) 
                  -> (s : Stack )
                  -> run (comp (Mult e1 e2)) s = run (comp (Mult e2 e1)) s
cmpMultCommutative (Const n1) (Const n2) s = rewrite multCommutative n1 n2 in Refl 

cmpMultCommutative (Const n1) (Plus e1 e2) s  with (mulPushComL n1 s e1 e2)
  cmpMultCommutative (Const n1) (Plus e1 e2) s | hypa = rewrite hypa in Refl

cmpMultCommutative (Const n1) (Mult e1 e2) s with (mulPushCom0 n1 s e1 e2)
    cmpMultCommutative (Const n1) (Mult e1 e2) s | hypa = rewrite hypa in Refl

cmpMultCommutative (Plus e1 e2) (Const n2) s with (mulPushComL2 n2 s e1 e2)
    cmpMultCommutative (Plus e1 e2) (Const n2) s | hypa = rewrite hypa in Refl 

cmpMultCommutative (Mult e1 e2) (Const n2) s with (mulPushComL3 n2 s e1 e2)
    cmpMultCommutative (Mult e1 e2) (Const n2) s | hypa = rewrite hypa in Refl

cmpMultCommutative (Plus e1 e2) (Plus e3 e4 ) s with (mulPushCom7 e1 e2 e3 e4 s)
    cmpMultCommutative (Plus e1 e2) (Plus e3 e4 ) s | hypa = rewrite hypa in Refl

cmpMultCommutative (Mult e1 e2) (Mult e3 e4) s with (mulPushCom8 e1 e2 e3 e4 s)
   cmpMultCommutative (Mult e1 e2) (Mult e3 e4) s | hypa = rewrite hypa in Refl

cmpMultCommutative (Plus e1 e2) (Mult e3 e4) s with (mulPushCom6 e1 e2 e3 e4 s) 
   cmpMultCommutative (Plus e1 e2) (Mult e3 e4) s | hypa = rewrite hypa in Refl 

cmpMultCommutative (Mult e1 e2) (Plus e3 e4) s with (mulPushCom9 e1 e2 e3 e4 s)
   cmpMultCommutative (Mult e1 e2) (Plus e3 e4) s | hypa = rewrite hypa in Refl

