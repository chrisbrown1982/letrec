module Instruction

%access public export

data Instruction : Type where
    PUSH    : Nat -> Instruction
    ADD     : Instruction
    SUB     : Instruction
    MUL     : Instruction
    DIV     : Instruction
    AND     : Instruction
    OR      : Instruction
    ISEQ    : Instruction
    ISGT    : Instruction
    ISGE    : Instruction
    JMP     : Nat -> Instruction
    JIF     : Nat -> Instruction
    LOAD    : Nat -> Instruction
    STORE   : Nat -> Instruction
    NOT     : Instruction
    HALT    : Instruction
    LABEL   : Nat -> Instruction

implementation Uninhabited (PUSH x = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = AND) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = OR) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (PUSH x = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = AND) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = OR) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (ADD = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = AND) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = OR) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (SUB = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = AND) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = OR) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (MUL = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = AND) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = OR) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (DIV = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (AND = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (AND = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (AND = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (AND = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (AND = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (AND = OR) where
    uninhabited Refl impossible
implementation Uninhabited (AND = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (AND = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (AND = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (AND = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (AND = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (AND = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (AND = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (AND = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (AND = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (AND = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (OR = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (OR = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (OR = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (OR = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (OR = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (OR = AND) where
    uninhabited Refl impossible
implementation Uninhabited (OR = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (OR = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (OR = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (OR = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (OR = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (OR = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (OR = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (OR = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (OR = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (OR = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = AND) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = OR) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (ISEQ = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = AND) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = OR) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (ISGT = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = AND) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = OR) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (ISGE = LABEL l) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = AND) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = OR) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = JIF y) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (JMP l = LABEL l2) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = AND) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = OR) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (JIF l = LABEL l2) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = AND) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = OR) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = JIF n) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = STORE n) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (LOAD l = LABEL l2) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = AND) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = OR) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = JIF n) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (STORE l = LABEL l2) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = AND) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = OR) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = JIF n) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = STORE l) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = HALT) where
    uninhabited Refl impossible
implementation Uninhabited (NOT = LABEL l2) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = AND) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = OR) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = JIF n) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = STORE l) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (HALT = LABEL l2) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = PUSH i) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = ADD) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = SUB) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = DIV) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = AND) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = MUL) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = OR) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = ISEQ) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = ISGT) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = ISGE) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = JMP y) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = JIF n) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = LOAD n) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = STORE l) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = NOT) where
    uninhabited Refl impossible
implementation Uninhabited (LABEL x = HALT) where
    uninhabited Refl impossible

implementation DecEq Instruction where
    decEq (PUSH x) (PUSH y) with (decEq x y)
       decEq (PUSH y) (PUSH y) | Yes Refl = Yes Refl
       decEq (PUSH x) (PUSH y) | No c = No (\Refl => c Refl)
    decEq ADD ADD = Yes Refl
    decEq SUB SUB = Yes Refl
    decEq MUL MUL = Yes Refl
    decEq DIV DIV = Yes Refl
    decEq AND AND = Yes Refl 
    decEq OR OR = Yes Refl 
    decEq ISEQ ISEQ = Yes Refl 
    decEq ISGT ISGT = Yes Refl
    decEq ISGE ISGE = Yes Refl 
    decEq (JMP s) (JMP s2) with (decEq s s2)
        decEq (JMP s2) (JMP s2) | Yes Refl = Yes Refl 
        decEq (JMP s) (JMP s2) | No c = No (\Refl => c Refl)
    decEq (JIF s) (JIF s2) with (decEq s s2)
        decEq (JIF s2) (JIF s2) | Yes Refl = Yes Refl 
        decEq (JIF s) (JIF s2) | No c = No (\Refl => c Refl) 
    decEq (LOAD x) (LOAD y) with (decEq x y)
        decEq (LOAD y) (LOAD y) | Yes Refl = Yes Refl
        decEq (LOAD x) (LOAD y) | No c = No (\Refl => c Refl)  
    decEq (STORE x) (STORE y) with (decEq x y)
        decEq (STORE y) (STORE y) | Yes Refl = Yes Refl
        decEq (STORE x) (STORE y) | No c = No (\Refl => c Refl)  
    decEq NOT NOT = Yes Refl 
    decEq HALT HALT = Yes Refl   
    decEq (LABEL s) (LABEL s2) with (decEq s s2)
        decEq (LABEL s2) (LABEL s2) | Yes Refl = Yes Refl 
        decEq (LABEL s) (LABEL s2) | No c = No (\Refl => c Refl) 
    decEq (PUSH x) ADD = No absurd
    decEq (PUSH x) SUB = No absurd
    decEq (PUSH x) MUL = No absurd
    decEq (PUSH x) DIV = No absurd
    decEq (PUSH x) AND = No absurd 
    decEq (PUSH x) OR = No absurd
    decEq (PUSH x) ISEQ = No absurd
    decEq (PUSH x) ISGT = No absurd
    decEq (PUSH x) ISGE = No absurd
    decEq (PUSH x) (JMP s2) = No absurd
    decEq (PUSH x) (JIF s2) = No absurd
    decEq (PUSH x)(LOAD y) = No absurd 
    decEq (PUSH x) (STORE y) = No absurd
    decEq (PUSH x) NOT = No absurd
    decEq (PUSH x) HALT = No absurd
    decEq (PUSH x) (LABEL s2) = No absurd 

    decEq ADD (PUSH i) = No absurd
    decEq ADD SUB = No absurd
    decEq ADD MUL = No absurd
    decEq ADD DIV = No absurd
    decEq ADD AND = No absurd 
    decEq ADD OR = No absurd
    decEq ADD ISEQ = No absurd
    decEq ADD ISGT = No absurd
    decEq ADD ISGE = No absurd
    decEq ADD (JMP s2) = No absurd
    decEq ADD (JIF s2) = No absurd
    decEq ADD (LOAD y) = No absurd 
    decEq ADD (STORE y) = No absurd
    decEq ADD NOT = No absurd
    decEq ADD HALT = No absurd
    decEq ADD (LABEL s2) = No absurd  

    decEq SUB (PUSH i) = No absurd
    decEq SUB ADD = No absurd
    decEq SUB MUL = No absurd
    decEq SUB DIV = No absurd
    decEq SUB AND = No absurd 
    decEq SUB OR = No absurd
    decEq SUB ISEQ = No absurd
    decEq SUB ISGT = No absurd
    decEq SUB ISGE = No absurd
    decEq SUB (JMP s2) = No absurd
    decEq SUB (JIF s2) = No absurd
    decEq SUB (LOAD y) = No absurd 
    decEq SUB (STORE y) = No absurd
    decEq SUB NOT = No absurd
    decEq SUB HALT = No absurd
    decEq SUB (LABEL s2) = No absurd 

    decEq MUL (PUSH i) = No absurd
    decEq MUL ADD = No absurd
    decEq MUL SUB = No absurd
    decEq MUL DIV = No absurd
    decEq MUL AND = No absurd 
    decEq MUL OR = No absurd
    decEq MUL ISEQ = No absurd
    decEq MUL ISGT = No absurd
    decEq MUL ISGE = No absurd
    decEq MUL (JMP s2) = No absurd
    decEq MUL (JIF s2) = No absurd
    decEq MUL (LOAD y) = No absurd 
    decEq MUL (STORE y) = No absurd
    decEq MUL NOT = No absurd
    decEq MUL HALT = No absurd
    decEq MUL (LABEL s2) = No absurd 

    decEq DIV (PUSH i) = No absurd
    decEq DIV ADD = No absurd
    decEq DIV SUB = No absurd
    decEq DIV MUL = No absurd
    decEq DIV AND = No absurd 
    decEq DIV OR = No absurd
    decEq DIV ISEQ = No absurd
    decEq DIV ISGT = No absurd
    decEq DIV ISGE = No absurd
    decEq DIV (JMP s2) = No absurd
    decEq DIV (JIF s2) = No absurd
    decEq DIV(LOAD y) = No absurd 
    decEq DIV (STORE y) = No absurd
    decEq DIV NOT = No absurd
    decEq DIV HALT = No absurd
    decEq DIV (LABEL s2) = No absurd 

    decEq AND (PUSH i) = No absurd
    decEq AND ADD = No absurd
    decEq AND SUB = No absurd
    decEq AND MUL = No absurd
    decEq AND DIV = No absurd
    decEq AND OR = No absurd
    decEq AND ISEQ = No absurd
    decEq AND ISGT = No absurd
    decEq AND ISGE = No absurd
    decEq AND (JMP s2) = No absurd
    decEq AND (JIF s2) = No absurd
    decEq AND (LOAD y) = No absurd 
    decEq AND (STORE y) = No absurd
    decEq AND NOT = No absurd
    decEq AND HALT = No absurd
    decEq AND (LABEL s2) = No absurd  

    decEq OR (PUSH i) = No absurd
    decEq OR ADD = No absurd
    decEq OR SUB = No absurd
    decEq OR MUL = No absurd
    decEq OR DIV = No absurd
    decEq OR AND = No absurd 
    decEq OR ISEQ = No absurd
    decEq OR ISGT = No absurd
    decEq OR ISGE = No absurd
    decEq OR (JMP s2) = No absurd
    decEq OR (JIF s2) = No absurd
    decEq OR (LOAD y) = No absurd 
    decEq OR (STORE y) = No absurd
    decEq OR NOT = No absurd
    decEq OR HALT = No absurd
    decEq OR (LABEL s2) = No absurd 

    decEq ISEQ (PUSH i) = No absurd
    decEq ISEQ ADD = No absurd
    decEq ISEQ SUB = No absurd
    decEq ISEQ DIV = No absurd
    decEq ISEQ MUL = No absurd
    decEq ISEQ AND = No absurd 
    decEq ISEQ OR = No absurd
    decEq ISEQ ISGT = No absurd
    decEq ISEQ ISGE = No absurd
    decEq ISEQ (JMP s2) = No absurd
    decEq ISEQ (JIF s2) = No absurd
    decEq ISEQ (LOAD y) = No absurd 
    decEq ISEQ (STORE y) = No absurd
    decEq ISEQ NOT = No absurd
    decEq ISEQ HALT = No absurd
    decEq ISEQ (LABEL s2) = No absurd 

    decEq ISGT (PUSH i) = No absurd
    decEq ISGT ADD = No absurd
    decEq ISGT SUB = No absurd
    decEq ISGT MUL = No absurd
    decEq ISGT DIV = No absurd
    decEq ISGT AND = No absurd 
    decEq ISGT OR = No absurd
    decEq ISGT ISEQ = No absurd
    decEq ISGT ISGE = No absurd
    decEq ISGT (JMP s2) = No absurd
    decEq ISGT (JIF s2) = No absurd
    decEq ISGT (LOAD y) = No absurd 
    decEq ISGT (STORE y) = No absurd
    decEq ISGT NOT = No absurd
    decEq ISGT HALT = No absurd
    decEq ISGT (LABEL s2) = No absurd 

    decEq ISGE (PUSH i) = No absurd
    decEq ISGE ADD = No absurd
    decEq ISGE SUB = No absurd
    decEq ISGE MUL = No absurd
    decEq ISGE DIV = No absurd
    decEq ISGE AND = No absurd 
    decEq ISGE OR = No absurd
    decEq ISGE ISEQ = No absurd
    decEq ISGE ISGT = No absurd
    decEq ISGE (JMP s2) = No absurd
    decEq ISGE (JIF s2) = No absurd
    decEq ISGE (LOAD y) = No absurd 
    decEq ISGE (STORE y) = No absurd
    decEq ISGE NOT = No absurd
    decEq ISGE HALT = No absurd
    decEq ISGE (LABEL s2) = No absurd  

    decEq (JMP l) (PUSH i) = No absurd
    decEq (JMP l) ADD = No absurd
    decEq (JMP l) SUB = No absurd
    decEq (JMP l) MUL = No absurd
    decEq (JMP l) DIV = No absurd
    decEq (JMP l) AND = No absurd 
    decEq (JMP l) OR = No absurd
    decEq (JMP l) ISEQ = No absurd
    decEq (JMP l) ISGT = No absurd
    decEq (JMP l) ISGE = No absurd
    decEq (JMP l) (JIF s2) = No absurd
    decEq (JMP l) (LOAD y) = No absurd 
    decEq (JMP l) (STORE y) = No absurd
    decEq (JMP l) NOT = No absurd
    decEq (JMP l) HALT = No absurd
    decEq (JMP l) (LABEL s2) = No absurd 

    decEq (JIF l) (PUSH i) = No absurd
    decEq (JIF l) ADD = No absurd
    decEq (JIF l) SUB = No absurd
    decEq (JIF l) MUL = No absurd
    decEq (JIF l) DIV = No absurd
    decEq (JIF l) AND = No absurd 
    decEq (JIF l) OR = No absurd
    decEq (JIF l) ISEQ = No absurd
    decEq (JIF l) ISGT = No absurd
    decEq (JIF l) ISGE = No absurd
    decEq (JIF l) (JMP s2) = No absurd
    decEq (JIF l) (LOAD y) = No absurd 
    decEq (JIF l) (STORE y) = No absurd
    decEq (JIF l) NOT = No absurd
    decEq (JIF l) HALT = No absurd
    decEq (JIF l) (LABEL s2) = No absurd 

    decEq (LOAD l) (PUSH i) = No absurd
    decEq (LOAD l) ADD = No absurd
    decEq (LOAD l) SUB = No absurd
    decEq (LOAD l) MUL = No absurd
    decEq (LOAD l) AND = No absurd 
    decEq (LOAD l) DIV = No absurd
    decEq (LOAD l) OR = No absurd
    decEq (LOAD l) ISEQ = No absurd
    decEq (LOAD l) ISGT = No absurd
    decEq (LOAD l) ISGE = No absurd
    decEq (LOAD l) (JMP s2) = No absurd
    decEq (LOAD l) (JIF s2) = No absurd
    decEq (LOAD l) (STORE y) = No absurd
    decEq (LOAD l) NOT = No absurd
    decEq (LOAD l) HALT = No absurd
    decEq (LOAD l) (LABEL s2) = No absurd 

    decEq (STORE n) (PUSH i) = No absurd
    decEq (STORE n) ADD = No absurd
    decEq (STORE n) SUB = No absurd
    decEq (STORE n) MUL = No absurd
    decEq (STORE n) DIV = No absurd
    decEq (STORE n) AND = No absurd
    decEq (STORE n) OR = No absurd
    decEq (STORE n) ISEQ = No absurd
    decEq (STORE n) ISGT = No absurd
    decEq (STORE n) ISGE = No absurd
    decEq (STORE n) (JMP s2) = No absurd
    decEq (STORE n) (JIF s2) = No absurd
    decEq (STORE n) (LOAD y) = No absurd 
    decEq (STORE n) NOT = No absurd
    decEq (STORE n) HALT = No absurd
    decEq (STORE n) (LABEL s2) = No absurd  

    decEq NOT (PUSH i) = No absurd
    decEq NOT ADD = No absurd
    decEq NOT SUB = No absurd
    decEq NOT MUL = No absurd
    decEq NOT DIV = No absurd
    decEq NOT AND = No absurd 
    decEq NOT OR = No absurd
    decEq NOT ISEQ = No absurd
    decEq NOT ISGT = No absurd
    decEq NOT ISGE = No absurd
    decEq NOT (JMP s2) = No absurd
    decEq NOT (JIF s2) = No absurd
    decEq NOT (LOAD y) = No absurd 
    decEq NOT (STORE y) = No absurd
    decEq NOT HALT = No absurd
    decEq NOT (LABEL s2) = No absurd 

    decEq HALT (PUSH i) = No absurd
    decEq HALT ADD = No absurd
    decEq HALT SUB = No absurd
    decEq HALT MUL = No absurd
    decEq HALT DIV = No absurd
    decEq HALT AND = No absurd 
    decEq HALT OR = No absurd
    decEq HALT ISEQ = No absurd
    decEq HALT ISGT = No absurd
    decEq HALT ISGE = No absurd
    decEq HALT (JMP s2) = No absurd
    decEq HALT (JIF s2) = No absurd
    decEq HALT (LOAD y) = No absurd 
    decEq HALT (STORE y) = No absurd
    decEq HALT NOT = No absurd
    decEq HALT (LABEL s2) = No absurd 

    decEq (LABEL l) (PUSH i) = No absurd
    decEq (LABEL l) ADD = No absurd
    decEq (LABEL l) SUB = No absurd
    decEq (LABEL l) DIV = No absurd
    decEq (LABEL l) MUL = No absurd
    decEq (LABEL l) AND = No absurd 
    decEq (LABEL l) OR = No absurd
    decEq (LABEL l) ISEQ = No absurd
    decEq (LABEL l) ISGT = No absurd
    decEq (LABEL l) ISGE = No absurd
    decEq (LABEL l) (JMP s2) = No absurd
    decEq (LABEL l) (JIF s2) = No absurd
    decEq (LABEL l) (LOAD y) = No absurd 
    decEq (LABEL l) (STORE y) = No absurd
    decEq (LABEL l) NOT = No absurd
    decEq (LABEL l) HALT = No absurd