module SOL where

import Data.List
import Data.Maybe

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp key = fromJust . lookup key

-- 3 marks
--Gives the list of variables in a formula
vars :: Formula -> [Id]
vars = sort . nub . varsy
    where
        varsy :: Formula -> [Id]
        varsy (Var x) = [x]
        varsy (Not f) =  vars f
        varsy (And f1 f2) = vars f1 ++ vars f2
        varsy (Or f1 f2) = vars f1 ++ vars f2

-- 1 mark
--Numbers the list of variables, list of tuples
idMap :: Formula -> IdMap
idMap f = zip (vars f) [1..]

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (And f1 f2)) = Or (toNNF $ Not f1) (toNNF $ Not f2)
toNNF (Not (Or f1 f2)) = And (toNNF $ Not f1) (toNNF $ Not f2)
toNNF (Not (Not f)) = toNNF f
toNNF (And f1 f2) = And (toNNF f1) (toNNF f2)
toNNF (Or f1 f2) = Or (toNNF f1) (toNNF f2)
toNNF f = f


-- 3 marks
--CNF is essentially canonical maxterm
toCNF :: Formula -> CNF
toCNF f = case (toNNF f) of
    Or f1 f2 -> distribute (toCNF f1) (toCNF f2)
    And f1 f2 -> And (toCNF f1) (toCNF f2)
    _ -> f

-- 4 marks
--Takes a CNF formula and flattens it
flatten :: CNF -> CNFRep --[[Int]]
flatten cnf = flatteny cnf indexes
    where
        indexes = idMap cnf
        flatteny :: CNF -> IdMap -> CNFRep
        flatteny cnf indexes = case cnf of
            And f1 f2 -> flatteny f1 indexes ++ flatteny f2 indexes
            Or f1 f2 -> [concat (flatteny f1 indexes ++ flatteny f2 indexes)]
            Not f -> map (map negate) $ flatteny f indexes
            Var x -> [[lookUp x indexes]]

--------------------------------------------------------------------------
-- Part III

-- 5 marks
{-
By implementing the rules described in Section 4.1, and illustrated in Section 4.2, define a
function propUnits :: CNFRep -> (CNFRep, [Int]) that will take the flattened version
of a CNF and return a pair comprising:
• The CNFRep that results from propagating all unit clauses in the original CNFRep
• The list of all unit clauses propagated as part of this process
By definition, the CNFRep returned in the result pair should contain no unit clauses.
Note that a unit clause in a CNFRep is a singleton list comprising just an integer, which may
be positive or negative, depending on whether or not the corresponding variable is negated,
as described in Section 2.2. For example:
*SAT> propUnits []
([],[])
*SAT> cnf1Rep
[[1,2,3],[1,2,-3],[1,-2,3],[1,-2,-3],[-1,2,3],[-1,2,-3],[-1,-2,3]]
*SAT> propUnits cnf1Rep
([[1,2,3],[1,2,-3],[1,-2,3],[1,-2,-3],[-1,2,3],[-1,2,-3],[-1,-2,3]],[])
*SAT> cnf2Rep
[[-1,-4],[2,1,5],[3,-2],[4],[3,-5],[-3,-7],[1,7,6],[-3,6]]
*SAT> propUnits cnf2Rep
([[2,5],[3,-2],[3,-5],[-3,-7],[7,6],[-3,6]],[4,-1])
The order of the elements in the resulting lists and sublists is unimportant.
Hint: It’s easier if you propagate one unit clause at a time, i.e. if a CNF has multiple unit
clauses then select one of them to propagate. The others will be picked up by recursion.
-}
-- Check for a singlton list
-- It must be true, so can remove from the ands
-- And can remove the not of it from the ors
-- Do this until no singletons
-- Now can brute force by taking first literal and assume to be true
-- Also, assume it to be false, call two recursive things of the dp algorithm
-- Same process for this
-- May have new singletons, obvious what to do next
-- If you get an empty list that is success, so return list of list of unit clauses propagated
-- Also concatenate unit clauses taken to be true before these recursive calls

--propUnits just the singleton part, not the adding singletons
propUnits :: CNFRep -> (CNFRep, [Int]) --CNF after propagating and the list of inital unit clauses
propUnits cnf = (assume_list next_singletons next, singletons ++ next_singletons)
    where
        isSingleton :: [a] -> Bool
        isSingleton [_] = True
        isSingleton _ = False

        find_singletons :: CNFRep -> [Int]
        find_singletons = concat . (filter isSingleton)

        assume :: CNFRep -> Int -> CNFRep
        assume cnf literal = map (filter (/=(negate literal))) (filter (/=[literal]) cnf)

        assume_list :: [Int] -> CNFRep -> CNFRep
        assume_list [] cnf = cnf
        assume_list singletons cnf = foldl' assume cnf singletons

        singletons = find_singletons cnf
        next = assume_list singletons cnf
        next_singletons = find_singletons next

-- 4 marks
dp :: CNFRep -> [[Int]]
dp 
  = undefined

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat
  = undefined


