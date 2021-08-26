module Simple 

%access public export

data Arith = Num Nat
           | Plus Arith Arith 
           
data StackOp = SNum Nat 
             | SPlus 

eval : List Nat -> List StackOp -> Either (List Nat, List StackOp) Nat 
eval (n::ns) [] = Right n 
eval ns (SNum n::xs) = eval (n::ns) xs 
eval (n1::n2::ns) (SPlus::xs) = eval (n1+n2::ns) xs 
eval vals instrs = Left (vals, instrs)


eval' : Arith -> Nat 
eval' (Num n) = n 
eval' (Plus a1 a2) = (eval' a1) + (eval' a2)


compile : Arith -> List StackOp 
compile (Num n) = [ SNum n]
compile (Plus a1 a2) = compile a1 ++ compile a2 ++ [SPlus]

hypa : (a : Arith)
    -> (s : List Nat)
    -> eval s (compile a) = eval (eval' a :: s) []

cmpCorrectStack : (a : Arith)
               -> (s : List Nat)
               -> eval s (compile a ++ xs) = eval (eval' a :: s) xs
cmpCorrectStack (Num n) s = Refl
cmpCorrectStack (Plus a1 a2) s = ?goal2


cmpCorrect : (a : Arith)
          -> eval [] (compile a ++ xs) = eval [eval' a] xs
cmpCorrect a = cmpCorrectStack a []
-- eval_step (Plus a1 a2) xs with (eval_step a1 xs)
 --   eval_step (Plus a1 a2) xs | iHA1 with (eval_step a2 xs)
   --     eval_step (Plus a1 a2) xs | iHA1 | iHA2 = ?e2

proveNil : (a : Arith) -> eval s (compile a) = Right (eval' a) 
proveNil (Num n) = Refl
proveNil (Plus a1 a2) with (proveNil a1)
    proveNil (Plus a1 a2) | a with (proveNil a2)
        proveNil (Plus a1 a2) | a | b = ?h2 