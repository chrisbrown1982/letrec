module Simple2 

%access public export

data Expr = Const Nat | Plus Expr Expr 

eval : Expr -> Nat 
eval (Const n) = n 
eval (Plus e1 e2) = eval e1 + eval e2

evalPlusCommutative : (e1, e2 : Expr) -> eval (Plus e1 e2) = eval (Plus e2 e1)
evalPlusCommutative (Plus e1 e2) (Plus e3 e4) with (eval e1)
    evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa with (eval e2)
        evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa | hypb with (eval e3)
            evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa | hypb | hypc with (eval e4)
                evalPlusCommutative (Plus e1 e2) (Plus e3 e4) | hypa | hypb | hypc | hypd = 
                    rewrite plusCommutative (plus hypa hypb) (plus hypc hypd) in Refl


evalPlusCommutative (Plus e1 e2) (Const n) with (eval e1)
    evalPlusCommutative (Plus e1 e2) (Const n) | hypa with (eval e2)
        evalPlusCommutative (Plus e1 e2) (Const n) | hypa | hypb = 
            rewrite plusCommutative (plus hypa hypb) n in Refl

evalPlusCommutative (Const n) (Plus e3 e4) with (eval e3) 
    evalPlusCommutative (Const n) (Plus e3 e4) | hypa with (eval e4) 
        evalPlusCommutative (Const n) (Plus e3 e4) | hypa | hypb = 
            rewrite plusCommutative n (plus hypa hypb) in Refl

evalPlusCommutative (Const n1) (Const n2) = 
    rewrite plusCommutative n1 n2 in Refl



Stack : Type 
Stack = List Nat 

data Instr = Push Nat | Add 

Prog : Type 
Prog = List Instr 

exec : Instr -> Stack -> Stack 
exec (Push k) s = k :: s 
exec Add (i :: j :: s) = j + i :: s 
exec Add s = s 

execCommute : (i, j : Nat)
           -> (s : Stack) 
           -> exec Add (i::j::s) = exec Add (j::i::s)
execCommute i j s = rewrite plusCommutative i j in Refl


run : Prog -> Stack -> Stack 
run [] s = s 
run (instr :: rest) s = run rest $ exec instr s 

comp : Expr -> Prog 
comp (Const n) = [Push n]
comp (Plus e1 e2) = comp e1 ++ comp e2 ++ [Add]

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
       --   where 
  
cmpCorrect :  (e : Expr) 
           -> run (comp e) [] = [eval e]
cmpCorrect e = cmpCorrectStack e []

cmpa : (e1, e2 : Expr)
     -> (n1 : Nat)
     -> (s : Stack)
     -> run ((comp e1 ++ comp e2 ++ [Add]) ++ [Add]) (n1 :: s) = run ((comp e1 ++ comp e2 ++ [Add]) ++ [Push n1, Add]) s
cmpa e1 e2 n1 s = ?goala


prf44 :  (n, n1,k : Nat)
    -> (r : Instr)
    ->   exec r ([k, plus n1 n]) = exec r (n1 :: exec r ([k,n]))
prf44 n n1 k Add = 
    rewrite plusCommutative n1 n in
        rewrite plusCommutative (plus n n1) k in 
            rewrite plusAssociative k n n1 in 
                rewrite plusCommutative k n in Refl

prf4 :  (n, n1 : Nat)
    -> (r1 : Instr)
    ->   exec r1 (plus n1 n :: []) = exec r1 (n1 :: exec Add (n :: []))
prf4 n n1 Add = rewrite plusCommutative n n1 in Refl


prf200 :  (rest : Prog)
       -> (n, k, n1 : Nat)
       -> run (rest1 ++ [Push (plus n k), Add]) [n1] = run (rest1 ++ [Push n1, Add]) [plus n k]
prf200 rest1 n k n1 with (run (rest1 ++ [Push n1, Add]) [plus n k])
    prf200 rest1 n k n1 | hypa with (runPartial rest1 [Push (plus n k), Add] [n1])
       prf200 rest1 n k n1 | hypa | hypb = ?jjo

mutual
    prf100 : (k, n1, n : Nat)
        -> (r : Instr)
        -> (rest : Prog)
        -> exec Add (run (r::rest) [k, plus n1 n]) = run ((r::rest) ++ [Push n1, Add]) [k, n]
    prf100 k n1 n Add [] = rewrite plusCommutative n1 n in 
                                rewrite plusCommutative (plus n n1) k in 
                                    rewrite plusAssociative k n n1 in 
                                        rewrite plusCommutative k n in Refl
    prf100 k n1 n Add (Add::rest1) with (prf4 (plus n1 n) k Add)
        prf100 k n1 n Add (Add::rest1) | hypa with (prf44 n n1 k Add)
            prf100 k n1 n Add (Add::rest1) | hypa | hypb with (prof99 (plus n k) n1 rest1)
                prf100 k n1 n Add (Add::rest1) | hypa | hypb | hypc 
                    = rewrite plusCommutative (plus n1 n) k in 
                        rewrite hypa in rewrite hypb in 
                            rewrite hypc in ?bob2


    prof99 :  (n1, n : Nat)
        -> (rest : Prog)
        -> exec Add (run rest [plus n1 n]) = run (rest ++ [Push n1, Add]) [n]
    prof99 n1 n [] = rewrite plusCommutative n1 n in Refl
    prof99 n1 n (Add::rest) with (prof99 n1 n rest) 
        prof99 n1 n (Add::rest) | hypa = rewrite hypa in Refl
    prof99 n1 n (Push k::rest) with (prf100 k n1 n Add rest ) 
        prof99 n1 n (Push k ::rest) | hypa = ?help -- with (prof99 n1 n rest) 


prf5 : (r : Instr)
     -> (n, n1 : Nat)
     -> (rest : Prog)
     -> exec Add (run rest (exec r [plus n1 n])) = run (rest ++ [Push n1, Add]) (exec r [n])
prf5 Add n n1 rest = ?k -- with (run (rest ++ [Push n1, Add]) (exec Add [n]))
   -- prf5 Add n n1 rest | hypa = ?k

prf6 : (r : Instr)
    -> (k : Nat)
    -> (n, n1 : Nat)
    -> (rest : Prog)
    -> exec Add (run rest (exec r [k, plus n1 n])) = run (rest ++ [Push n1, Add]) (exec r [k, n])
prf6 Add k n n1 [] with (prf44 n n1 k Add) 
    prf6 Add k n n1 [] | hypa = 
        rewrite hypa in Refl -- with (prf6 r k n1 n )= ?six
prf6 Add k n n1 (r1::rest)= ?six2

prf3 : (n, n1 : Nat)
    -> (s : Stack )
    -> (rest : Prog)
    -> exec Add (run rest (plus n1 n :: s)) = run (rest ++ [Push n1, Add]) (exec Add (n :: s))
prf3 n n1 [] [] = rewrite plusCommutative n1 n in Refl
prf3 n n1 (s1::ss) [] = rewrite plusCommutative n1 n in rewrite plusAssociative s1 n n1 in Refl
prf3 n n1 [] (Add::rest) with (prf3 n n1 [] rest)
    prf3 n n1 [] (Add::rest) | hypa = rewrite hypa in Refl -- rewrite plusCommutative n1 n in ?kk 
prf3 n n1 [] (Push k::rest) = ?g4     
prf3 n n1 (s1::ss) (Add::rest) = ?g5


prf2 :  (n, n1 : Nat)
     -> (s : Stack)
     -> (rest : Prog)
     -> exec Add (run rest (n :: n1 :: s)) = run (rest ++ [Push n1, Add]) (n :: s)
prf2 n n1 s [] = rewrite plusCommutative n1 n in Refl
prf2 n n1 s (Add::rest)   = ?f2
prf2 n n1 s (Push k::rest) = ?f3

prf1 : (n1 : Nat)
     -> (s : Stack)
     -> (instr : Instr)
     -> (rest : Prog)
     -> exec Add (run rest (exec instr (n1 :: s))) = run (rest ++ [Push n1, Add]) (exec instr s)
prf1 n1 s (Push n) rest = ?goalPr
prf1 n1 s Add rest = ?goalPr2

cmpPartial : (p : Prog)
           -> (n1 : Nat)
           -> (s : Stack)
           -> run (p ++ [Add]) (n1::s) = run (p ++ [Push n1, Add]) s
cmpPartial [] n1 s = Refl
cmpPartial (instr::rest) n1 s with (runPartial rest [Add] (exec instr (n1::s))  )
    cmpPartial (instr::rest) n1 s | hypa = rewrite hypa in ?goalP --with (runPartial rest [Add] (exec instr (n1::s))  )?goalP -- with (cmpPartial instrs n1 $ exec instr s)

------------------------------------------------------------------------------------

cmpPlusCommutative : (e1, e2 : Expr) 
                  -> (s : Stack )
                  -> run (comp (Plus e1 e2)) s = run (comp (Plus e2 e1)) s
cmpPlusCommutative (Const n1) (Const n2) s = rewrite plusCommutative n1 n2 in Refl 

cmpPlusCommutative (Const n1) (Plus e1 e2) s = ?goal2
cmpPlusCommutative (Plus e1 e2) (Const n2) s = ?goal3 
cmpPlusCommutative (Plus e1 e2) (Plus e3 e4 ) s = ?goal4 
