{-------------------------------------------------------------------------------
 - Max Guo
 - November 21, 2011
 - DPLL Algorithm
 ------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------
 - TODO: - currently will always return an assignment mapping
 -             regardless of whether or not the mapping actually satisfies
 -             the CNF
 -       - only returns True assignments, False assignments left out of map
 ------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------
 - USAGE: - no main, so through ghci
 -        - :l Sat
 -        - working example: dpll (CNF [[1], [2, -1]])
 -        - broken example: dpll (CNF [[1], [2, -1], [-1]])
 -        - input assumed to already be in CNF
 -              CNF [[1], [2, -1]] is A ^ (B v ~A)
 ------------------------------------------------------------------------------}

{-# OPTIONS -Wall -fwarn-tabs #-} 
module Sat where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List

-- An expression in CNF, the conjunction of clauses
newtype CNF = CNF [Clause] deriving (Eq, Ord, Show)
unCNF :: CNF -> [Clause]
unCNF (CNF cs) = cs

-- A clause -- the disjunction of a number of literals
type Clause = [Lit]

-- A literal, either a positive or negative variable
type Lit = Int 

-- invert the polarity of a literal
invert :: Lit -> Lit
invert a = negate a

valid :: Map Lit Bool  -> Bool
valid m = Map.foldrWithKey (\ lit b1 val -> 
                              case Map.lookup (invert lit) m of 
                                 Just b2 -> b1 == not b2 && val
                                 Nothing -> True && val) True m

interp :: (Map Lit Bool) -> CNF -> Bool
interp m (CNF f) = all (any (findLit m)) f where
  findLit m' k = 
     case (Map.lookup k m', Map.lookup (invert k) m') of
          (Just b1, Just b2) | b1 == not b2 -> b1
          (Just _, Just  _)  -> error "invalid map"
          (Just b, Nothing)  -> b
          (Nothing, Just b)  -> not b
          (Nothing, Nothing) -> True  

dpll :: CNF -> Maybe (Map Lit Bool)
dpll (CNF []) = Just (Map.empty)
dpll b@(CNF c) =
    if [] `elem` c
        then Nothing
        else d' Map.empty (CNF c) where
             d' :: Map Lit Bool -> CNF -> Maybe (Map Lit Bool)
             d' m (CNF []) = if interp m b
                                 then Just m
                                 else Nothing
             d' m (CNF c') =                      
                 let (pm, pc) = pureLitAssign (CNF c')
                     (um, uc) = unitPropagate pc
                     m' = Map.unions [um, pm, m]
                     x = unCNF uc in                                 

                 if length x > 1
                     then case satisfy (head x) of
                         Nothing -> Nothing
                         Just a -> if (valid (Map.union m' a))
                                       then d' (Map.union m' a) (CNF (tail x))
                                       else d' (Map.union m'
                                                   (Map.fromList
                                                   [(invert . fst . head $
                                                   Map.toList a, True)]))
                                               (CNF (tail x))
                     else Just m'

{-------------------------------------------------------------------------------
 - Given a list of literals, create the trivial assignment 
 - that satisfies that list (if one exists). 
 ------------------------------------------------------------------------------}
satisfy :: Clause -> Maybe (Map Lit Bool)
satisfy [] = Nothing
satisfy (c:_) = Just (Map.fromList [(c, True)])

{-------------------------------------------------------------------------------
 - If a propositional variable occurs with only one polarity in the
 - formula, it is called pure. Pure literals can always be assigned in
 - a way that makes all clauses containing them true. Thus, these
 - clauses do not constrain the search anymore and can be deleted. 
 - This function collects all pure literals from the formula and 
 - returns the assignment paired with the refactored formula 
 - that reflects that assignment.
 ------------------------------------------------------------------------------}
pureLitAssign :: CNF -> (Map Lit Bool, CNF)
pureLitAssign c = (m, (CNF y)) where 
                  m = Map.fromList (foldr (\x a -> (x, True):a) [] (getPure c))
                  y = stripPure m [] c

stripPure :: Map Lit Bool -> [Clause] -> CNF -> [Clause]
stripPure m a (CNF (c:cs)) = if c `intersect` k /= []
                                 then stripPure m a (CNF cs)
                                 else stripPure m (c:a) (CNF cs)
                             where k = Map.keys m
stripPure _ a (CNF []) = a

getPure :: CNF -> [Lit]
getPure (CNF c) = checkInvert m m where
                  checkInvert :: [Lit] -> [Lit] -> [Lit]
                  checkInvert _ [] = []
                  checkInvert l1 (x:xs) = if (invert x) `notElem` l1
                                              then x:checkInvert l1 xs
                                              else checkInvert l1 xs

                  m = nub $ concat c

{-------------------------------------------------------------------------------
 - If a clause is a unit clause, i.e. it contains only a single
 - unassigned literal, this clause can only be satisfied by assigning
 - the necessary value to make this literal true. This function collects
 - all unit clauses from the formula and returns the assignment paired 
 - with the refactored formula that reflects that assignment.
 ------------------------------------------------------------------------------}
unitPropagate :: CNF -> (Map Lit Bool, CNF)
unitPropagate c = uP Map.empty c where
                  uP :: Map Lit Bool -> CNF -> (Map Lit Bool, CNF)
                  uP m c' = 
                      if (foldr (\x a -> (length x > 1) && (x \\ Map.keys m == x) && a) True (unCNF c'))
                          then (m, c')
                          else uP (fst b) (snd b) where
                                b = assignUnit m [] c'

assignUnit :: Map Lit Bool -> [Clause] -> CNF -> (Map Lit Bool, CNF)
assignUnit a1 a2 (CNF (a:as)) =
    if length a == 1
        then if (head a) `Map.member` a1 ||
                (invert (head a)) `Map.member` a1
                 then assignUnit a1 a2 (CNF as)
                 else assignUnit (Map.insert (head a) True a1) a2 (CNF as)
        else if k == []
                 then assignUnit a1 (a:a2) (CNF as)
                 else assignUnit a1 ((a \\ k):a2) (CNF as)
             where k = (Map.keys a1) `intersect` a
assignUnit a1 a2 (CNF []) = (a1, (CNF a2))

