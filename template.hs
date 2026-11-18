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
{-
To complete the DP algorithm, use the function propUnits to define a function dp ::
CNFRep -> [[Int]] that will return the list of all satisfying assignments for the given
CNFRep, as described in Section 4.
For example,
*SAT> dp cnf1Rep
[[1,2,3]]
*SAT> dp cnf2Rep
[[4,-1,2,3,-7,6],[4,-1,-2,5,3,-7,6]]
*SAT> dp cnf3Rep
[]
The order of the elements in the resulting lists and sublists is unimportant. Note that
cnf1Rep has only a single satisfying assignment and cnfRep3 has none. As described in
Section 4.2, cnf2Rep has three solutions, but two of them are implicitly encoded in the
assignment [4,-1,2,3,-7,6] where the variable corresponding to the number 5, i.e. e here,
can assume either the value F alse or T rue.
Hint: The termination conditions (Section 4.2) can be based on inspection of the CNF after
unit propagation via propUnits, noting, as in the example above, that if the given CNF is
[] then the CNF in the pair returned by propUnits will also be [].
-}
-- Now can brute force by taking first literal and assume to be true
-- Also, assume it to be false, call two recursive things of the dp algorithm
-- Same process for this
-- May have new singletons, obvious what to do next
-- If you get an empty list that is success, so return list of list of unit clauses propagated
-- Also concatenate unit clauses taken to be true before these recursive calls
-- Returns lists of lists of satisfying assignments
dp :: CNFRep -> [[Int]]
dp cnf = (prop_trues ++ trues ++ falses) : (dp ass_true ++ dp ass_false)
    where
        (propped_list, prop_trues) = propUnits cnf
        take_first_lit :: [[a]] -> [a]
        take_first_lit [[]] = []
        take_first_lit ((y:ys):xs) = [y]
        first_lit = take_first_lit propped_list

        (ass_true, trues, ass_false, falses) =
            if first_lit == [] 
                then
                    ([], [], [], [])
                else
                    let
                        (ass_true, trues) = propUnits (first_lit : cnf)
                        (ass_false, falses) = propUnits (map negate first_lit : cnf)
                    in (ass_true, trues, ass_false, falses)

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat
  = undefined


