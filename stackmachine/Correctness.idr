module Correctness

import StackMachine
import Lang

%access public export
%default total

runPartial : (p : Prog) 
          -> (q : Prog) 
          -> (s : Stack) 
          -> run (p ++ q) s = run q (run p s)
runPartial [] q s = Refl
runPartial (instr::instrs) q s = runPartial instrs q $ exec instr s

runa : (a, b : Expr)
    -> (s : Stack)
    -> run (comp a ++ comp b ++ [Add]) s = run (comp b ++ [Add]) (run (comp a) s)
runa a b s = runPartial (comp a) (comp b ++ [Add]) s

runb : (a, b : Expr)
    -> (s : Stack)
    ->  run (comp b ++ [Add]) (run (comp a) s) = run [Add] (run (comp b) (run (comp a) s))
runb a b s = runPartial (comp b) [Add] (run (comp a) s)

runMa : (a, b : Expr)
    -> (s : Stack)
    -> run (comp a ++ comp b ++ [Mul]) s = run (comp b ++ [Mul]) (run (comp a) s)
runMa a b s = runPartial (comp a) (comp b ++ [Mul]) s

runMb : (a, b : Expr)
    -> (s : Stack)
    ->  run (comp b ++ [Mul]) (run (comp a) s) = run [Mul] (run (comp b) (run (comp a) s))
runMb a b s = runPartial (comp b) [Mul] (run (comp a) s)

cmpCorrectStack : (e : Expr)
               -> (s : Stack)
               -> run (comp e) s = [eval e] ++ s 
cmpCorrectStack (Const n) s = Refl 
cmpCorrectStack (Plus e1 e2) s with (cmpCorrectStack e1 s)
    cmpCorrectStack (Plus e1 e2) s | hypa with (cmpCorrectStack e2 $ [eval e1] ++ s)
        cmpCorrectStack (Plus a b) s | hypa | hypb = rewrite runa a b s in 
                                                        rewrite runb a b s in
                                                            rewrite hypa in 
                                                                rewrite hypb in Refl
cmpCorrectStack (Mult e1 e2) s with (cmpCorrectStack e1 s)
    cmpCorrectStack (Mult e1 e2) s | hypa with (cmpCorrectStack e2 $ [eval e1] ++ s)
        cmpCorrectStack (Mult e1 e2) s | hypa | hypb = rewrite runMa e1 e2 s in 
                                                        rewrite runMb e1 e2 s in 
                                                            rewrite hypa in 
                                                                rewrite hypb in 
                                                                    Refl

cmpCorrect :  (e : Expr) 
           -> run (comp e) [] = [eval e]
cmpCorrect e = cmpCorrectStack e []
