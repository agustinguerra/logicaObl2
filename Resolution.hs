
module Resolution(sat, tau, valid, V, F(..), Statement, L(..), C, CSet, Clash) where

-----------------------------------------
-- Tipos de datos
-----------------------------------------
type V = String
data F = Atom V
       | Neg  F
       | Conj F F                  
       | Disy F F     
       | Imp  F F
       deriving(Eq)     

type Statement = ([F],F)

data L = LP V | LN V
         deriving (Eq)
type C    = [L]
type CSet = [C]
type Clash = (C,L,C,L)

--Constants for testing
p :: F
p = Neg (Atom "test")

p1 :: F
p1 = Disy (Neg (Atom "test")) (Atom "no test")

clausula1 = Disy (Atom "a") (Atom "a")
clausula3 = Atom "a"
clausula2 = Disy (Neg (Atom "c")) (Disy (Neg (Atom "d")) (Atom "f"))
clausula4 = Conj (Conj clausula1 clausula1) (clausula2)

conj1 = [(LN "primero"),(LP "segundo"),(LP "tercer")]
conj2 = [(LN "cuarto"),(LN "quinto"),(LP "tercer"),(LP "segundo")]
conj3 = [(LP "segundo"),(LN "primero")]
conj4 = []
conj5 = [(LN "cuarto"),(LN "quinto"),(LP "tercer"),(LP "segundo")]
conj6 = [(LN "cuarto"),(LN "tercer"),(LP "tercer"),(LP "segundo")]

cset1 = [conj1,conj2]
cset2 = [conj5,conj3]


-----------------------------------------
-- Funciones principales
-----------------------------------------
-- containsEmpty :: CSet -> Bool
-- containsEmpty [] = False
-- containsEmpty (x:xs) = (x == []) || (containsEmpty xs)

-- Pos: retorna True si la formula es SAT, o False si es UNSAT
sat :: F -> Bool
sat f = not (elem [] (resolveCSet (f2CSet f)))

saturarCSet :: CSet -> Int -> CSet
saturarCSet [] _ = []
saturarCSet (c:resto) lActual = 
  if (not(length (c:resto) == lActual)) 
    then (c):(clash c resto)++(saturarCSet resto ((length (c:resto)) + (length (clash c resto))))
    else (c:resto)
--Resolves multiple clashes and adds them to the resultant set
solveClashes :: [Clash] -> CSet
solveClashes []   = []
solveClashes (c:cs) = (resolveClash c):(solveClashes cs)
-- C contra todo el CSet da un CSet nuevo  
clash :: C -> CSet -> CSet
clash c [] = []
clash c (x:xs) = (solveClashes (findClashCC c x)) ++ (clash c xs)

--Check clash ONE C AGASINT ANOTHER C 
findClashCC :: C -> C -> [Clash]
findClashCC _ [] = []
findClashCC c1 c2 = 
  case (getClashingLiterals c1 c2) of {
    []   -> [];
    x:[] -> [(c1,x,c2,(negateLiteral x))];
    x:xs -> []
  }  

-- Gets the list of clashing literals given to Clauses
getClashingLiterals :: C -> C -> [L]
getClashingLiterals [] _ = []
getClashingLiterals (l:resto) c2 = 
  if (hasClashCL c2 l) then
    l:(getClashingLiterals resto c2)
  else
    (getClashingLiterals resto c2)

negateLiteral :: L -> L
negateLiteral (LN v) = LP v
negateLiteral (LP v) = LN v

-- Check clashes in a CSet
hasClashCSet :: CSet -> Bool
hasClashCSet [] = False
hasClashCSet (x:xs) = case (hasClashCCset x xs) of {
  True -> True;
  False -> hasClashCSet xs
} 

--Checks ONE C against a CSet for clashes
hasClashCCset :: C -> CSet -> Bool
hasClashCCset _ [] = False
hasClashCCset c (cs:xcs) = case (hasClashCC c cs) of {
  True -> True;
  False -> (hasClashCCset c xcs)
}

--Check clash ONE C AGASINT ANOTHER C
hasClashCC :: C -> C -> Bool
hasClashCC [] _ = False;
hasClashCC (l:resto) c2 = (hasClashCL c2 l) || hasClashCC resto c2


--Check clash ONE C AGAINST ONE L
hasClashCL :: C -> L -> Bool
hasClashCL [] l = False
hasClashCL (c:cs) l = 
  if (contains (c:cs) (negateLiteral l)) then
    True 
  else
    (hasClashCL cs l)

-- Resolves clashes INSIDE the same C's
resolveInsideClash :: CSet -> CSet
resolveInsideClash [] = []
resolveInsideClash (x:[]) = [x]
resolveInsideClash (x:xs) = 
  if checkInsideClash x 
    then ((cleanInsideClash x):(resolveInsideClash xs))
    else resolveInsideClash xs

--Check if the C is valid and then return the C
cleanInsideClash :: C -> C
cleanInsideClash [] = []
cleanInsideClash c1 = case (checkInsideClash c1) of {
  True -> c1;
  False -> []
}

--Check if the C is not clashed in inside
checkInsideClash :: C -> Bool
checkInsideClash [] = True
checkInsideClash (literal:resto) = 
  let negado = case literal of {
    LN l -> LP l;
    LP l -> LN l;
  } in
  if (contains resto negado) then
    False 
  else
    (checkInsideClash resto)
  

-- Pos: retorna True si la formula es Tautología, o False en caso contrario
tau :: F -> Bool
tau = undefined

-- Pos: retorna True si el razonamiento es válido, o False en caso contrario
valid :: Statement -> Bool
valid = undefined

-----------------------------------------
-- Formulas y Clausulas
-----------------------------------------
-- Pos: convierte una formula a un conjunto de clausulas
f2CSet :: F -> CSet
f2CSet c1 = cnf2CSet (f2cnf c1)

-- Pre: recibe una formula en FNC
-- Pos: convierte la FNC a un conjunto de clausulas
cnf2CSetRepe :: F -> CSet
cnf2CSetRepe (Atom c1) = [[LP c1]]
cnf2CSetRepe (Neg (Atom c1)) = [[LN c1]]  
cnf2CSetRepe (Conj c1 c2) = cnf2CSetRepe c1 ++ cnf2CSetRepe c2
cnf2CSetRepe (Disy c1 c2) = case c1 of {
  Atom r -> [ insert (auxFNC c2) (LP r) ];
  Neg k ->  [ insert (auxFNC c2) (LN (extractAtomNeg k))];
  _ -> []
}
cnf2CSetRepe _ = undefined

cnf2CSet :: F -> CSet
cnf2CSet = \f -> resolveInsideClash (sanitizeCSet (cnf2CSetRepe (f2cnf f)))

sanitizeCSet :: CSet -> CSet
sanitizeCSet []   = [];
sanitizeCSet (c:set) = 
  if isCInCSet c set then
    sanitizeCSet set
  else
    c:(sanitizeCSet set)

--Gets the list of V's
auxFNC :: F -> C
auxFNC (Atom c1) = [LP c1]
auxFNC (Neg c1) = [LN (extractAtomNeg c1)]
auxFNC (Disy c1 c2) = case c1 of {
  Atom r -> [LP r] ++ auxFNC c2;
  Neg k -> [LN (extractAtomNeg k)] ++ auxFNC c2;
  _ -> undefined
}
auxFNC _ = undefined

contains:: C -> L -> Bool
contains = \lista e -> case lista of {
                          [] -> False;
                          x:xs -> x == e || contains xs e
                      }

insert:: C -> L -> C
insert= \lista e -> 
  if (contains lista e) then 
    lista
  else 
    e:lista

isCContained:: C -> C -> Bool
isCContained [] _ = True
isCContained c1 [] = False
isCContained c1 c2 = case c1 of {
  x:xs -> case contains c2 x of {
    True -> isCContained xs c2;
    False -> False
  };
  _ -> undefined
}

isCEqual:: C -> C -> Bool
isCEqual = \c1 c2 ->
  (isCContained c1 c2) && (isCContained c2 c1)

isCInCSet:: C -> CSet -> Bool
isCInCSet [] _ = True
isCInCSet _ [] = False
isCInCSet x (y:ys) = case (isCEqual x y) of {
  True -> True;
  False -> isCInCSet x ys
}  
                    

-- Gets the V from inside a Neg
extractAtomNeg :: F -> V
extractAtomNeg (Atom c1) = c1
extractAtomNeg (Neg c1) = extractAtomNeg c1
extractAtomNeg _ = undefined

-- Pos: convierte una formula a FNC
f2cnf :: F -> F
f2cnf = distr . pushNeg . sustImp

sustImp :: F -> F
sustImp (Atom v)     = (Atom v)
sustImp (Neg a)      = Neg (sustImp a)
sustImp (a `Conj` b) = (sustImp a) `Conj` (sustImp b)
sustImp (a `Disy` b) = (sustImp a) `Disy` (sustImp b)
sustImp (a `Imp`  b) = (Neg (sustImp a)) `Disy` (sustImp b) 

pushNeg :: F -> F
pushNeg (Atom v)           = (Atom v)
pushNeg (Neg (a `Disy` b)) = (pushNeg (Neg a)) `Conj` (pushNeg (Neg b))
pushNeg (Neg (a `Conj` b)) = (pushNeg (Neg a)) `Disy` (pushNeg (Neg b))
pushNeg (Neg (Neg a))      = pushNeg a
pushNeg (Neg a)            = Neg (pushNeg a)
pushNeg (a `Conj` b)       = (pushNeg a) `Conj` (pushNeg b)
pushNeg (a `Disy` b)       = (pushNeg a) `Disy` (pushNeg b)

distr :: F -> F
distr (a `Disy` b) = distr' ((distr a) `Disy` (distr b))
  where 
  distr' (a `Disy` (b `Conj` c)) = (distr' (a `Disy` b)) `Conj` (distr' (a `Disy` c))
  distr' ((a `Conj` b) `Disy` c) = (distr' (a `Disy` c)) `Conj` (distr' (b `Disy` c))
  distr' a                       = a
distr (a `Conj` b) = (distr a) `Conj` (distr b)
distr a            = a  


-----------------------------------------
-- Procedimiento de Resolución
-----------------------------------------
-- Pre: recibe un conjunto de clausulas
-- Pos: si es SAT,   retorna el conjunto de clausulas saturado
--      si es UNSAT, retorna un conjunto de clausulas incluyendo la clausula vacía
resolveCSet :: CSet -> CSet
resolveCSet [] = []
resolveCSet c = saturarCSet c 0 --(length c) 
               
-- Pos: retorna la resolvente de un conflicto
resolveClash :: Clash -> C
resolveClash (c1,l1,c2,l2) = (mergeC (returnCWithoutL c1 l1) (returnCWithoutL c2 l2))

returnCWithoutL :: C -> L -> C
returnCWithoutL [] _ = []
returnCWithoutL (x:xs) l = case x == l of {
  True -> returnCWithoutL xs l;
  False -> (x:(returnCWithoutL xs l))
}

mergeC :: C -> C -> C
mergeC c [] = c
mergeC [] c = c
mergeC (x) (y:ys) = (mergeC (insert x y) ys)




----------------------------------------------------------------------------------
-- Pretty Printing
instance Show F where
  show (Atom v)       = v
  show (Neg (Neg a))  = "~" ++ show (Neg a)
  show (Neg (Atom v)) = "~ " ++ show (Atom v)
  show (Neg a)        = "~ (" ++ show a ++ ")"
  show (a `Conj` b)   = "(" ++ show a ++ ") /\\ (" ++ show b ++ ")"
  show (a `Disy` b)   = "(" ++ show a ++ ") \\/ (" ++ show b ++ ")"
  show (a `Imp` b)    = "(" ++ show a ++ ") --> (" ++ show b ++ ")"
  
instance Show L where  
  show (LN v)  = "~" ++ v
  show (LP v)  = v


false = (Atom "p") `Conj` (Neg (Atom "p"))
true  = false `Imp` false
con2 = true `Imp` false