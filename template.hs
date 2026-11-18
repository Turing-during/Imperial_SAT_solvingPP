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
    nnf -> nnf

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
propUnits cnf = propUnitsLoop cnf []
    where
        isSingleton :: [a] -> Bool
        isSingleton [_] = True
        isSingleton _ = False

        find_singletons :: CNFRep -> [Int]
        find_singletons = concat . (filter isSingleton)

        assume :: Int -> CNFRep -> CNFRep
        assume literal cnf = map (filter (/=(negate literal))) (filter (not . elem literal) cnf)

        propUnitsLoop :: CNFRep -> [Int] -> (CNFRep, [Int])
        propUnitsLoop cnf acc_units =
            let unit_literals = find_singletons cnf
            in case unit_literals of
                [] -> (cnf, acc_units)
                (unit:_) ->
                    let ass_list = assume unit cnf
                    in propUnitsLoop ass_list (unit : acc_units)
{-
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
        next_singletons = find_singletons nextpropUnits cnf = (assume_list next_singletons next, singletons ++ next_singletons)
    where
        isSingleton :: [a] -> Bool
        isSingleton [_] = True
        isSingleton _ = False

        find_singletons :: CNFRep -> [Int]
        find_singletons = concat . (filter isSingleton)
-}

-- 4 marks
-- Now can brute force by taking first literal and assume to be true
-- Also, assume it to be false, call two recursive things of the dp algorithm
-- Base case when propped list empty, here we want to return singleton list containing list of unit clauses propagated
-- May have new singletons, obvious what to do next
-- If you get an empty list that is success, so return list of list of unit clauses propagated
-- Also concatenate unit clauses taken to be true before these recursive calls
-- Returns lists of lists of satisfying assignments

-- Could've used guards and been way neater
dp :: CNFRep -> [[Int]]
dp cnf =
    let (propped_list, units) = propUnits cnf
    in if any null propped_list
           then []
           else case propped_list of
                    [] -> [units]
                    _ ->
                        let first_lit = head $ head propped_list
                        in map (units++)
                               (dp ([first_lit] : propped_list) ++
                               dp ([negate first_lit] : propped_list)
                               )
{-
let (propped_list, unit_clauses) = propUnits cnf in
dp cnf = case propped_list of
             [] -> ???
             _ -> dp
         where
             take_first_lit :: [[a]] -> [a]
             take_first_lit ((y:ys):xs) = [y]
-}
--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat
  = undefined


