{-# LANGUAGE LambdaCase #-}
module Control.Monad.HedgehogTest where
import Hedgehog
import Hedgehog.Gen hiding (map)
import Hedgehog.Internal.Gen (evalGen)
import qualified Hedgehog.Internal.Seed as Seed
import qualified Hedgehog.Internal.Tree as Tree
import Data.Functor.Identity
import Debug.Trace (trace)
import Hedgehog.Range (linear)
import Control.Monad (void)
import Control.Monad.Trans.Cont
import Data.List (minimumBy, deleteBy)
import Data.Ord (comparing)
import Data.Function (on)
import Control.Arrow (first)

shrinker :: forall a. (a -> Bool) -> Gen a -> IO a
shrinker oracle gen = do
  seed <- Seed.random
  case evalGen 100 seed gen of
      Just (Tree.TreeT (Identity (Tree.NodeT l r ))) | not (oracle l) -> minTree l r
      _ -> shrinker oracle gen

 where
    minTree :: a -> [Tree.Tree a] -> IO a
    minTree p (Tree.TreeT (Identity (Tree.NodeT l r )) : xs)
      | not (oracle l) = minTree l r
      | otherwise = minTree p xs
    minTree p [] = return p


loudOracle :: (Show a, Ord a, Num a) => (a, a) -> Bool
loudOracle (i, j) = trace (show (i,j)) (i+j < 5 || i < 2 || j < 2)

gen1_100 :: Gen (Int,Int)
gen1_100 = (,) <$> integral (linear 1 100) <*> integral (linear 1 100)


main :: IO ()
main = void (shrinker loudOracle gen1_100)


data Tree q a = Tree a (OrderedQueue q (Tree q a))
  deriving (Show, Eq, Functor)

class Delayable q where
  delay :: q -> q
instance (Delayable q, Ord q) => Applicative (Tree q) where
   pure a = Tree a (OrderedQueue mempty)
   ls@(Tree f fs) <*> rs@(Tree a as) = Tree (f a) (OrderedQueue $ fmap doTry both)
     where
       both = mergeQueue fs as

       doTry (n, q, Left tl) = (q, tl <*> doDelays n rs)
       doTry (n, q, Right tr) = (q, doDelays n ls <*> tr)

       doDelays n (Tree x0 (OrderedQueue xs))= Tree x0 (OrderedQueue (fmap (first delay) taken) <> OrderedQueue rest)
         where
           (taken, rest) = splitAt n xs

mergeQueue :: (Ord q) => OrderedQueue q a -> OrderedQueue q b -> [(Int, q, Either a b)]
mergeQueue (OrderedQueue l0) (OrderedQueue r0) = go 0 l0 0 r0
  where
    go _ [] n ys = [ (n, q, Right y) | (q,y) <- ys ]
    go n xs _ [] = [ (n, q, Left y) | (q,y) <- xs ]
    go tl xs@((ql,vl) : ls) tr ys@((qr,vr) : rs) = case compare ql qr of
      GT -> (tl, qr, Right vr) : go tl xs (tr+1) rs
      _ -> (tr, ql, Left vl) : go (tl+1) ls tr ys

binSearch :: (Monoid q) => Int  -- ^ allowed value closest to 0
          -> Int  -- ^ generated value
          -> Tree q Int
binSearch zero generatedValue = shrinkFrom generatedValue $ do
  -- Small DSL to propose smaller values than generatedValue

  -- if 0 succeeds we are done
  tryMinimum mempty zero
  -- if the number is negative and positive works as well, go with that
  base <- if generatedValue < 0
          then tryTransform mempty negate generatedValue
          else pure generatedValue

  -- do a binary search towards 0
  let
   go l h
     | l > h = pure ()
     | otherwise = do
       let mid = (l + h) `div` 2
       yield mempty mid >>= \case
           -- Worked, try going even lower
           True -> go l (mid-1)
           -- didn't work
           False -> go (mid+1) h

  -- We already know 0 doesn't work and that generatedValue does
  if base > 0
  then go (zero+1) (base-1)
  else go (base+1) (zero-1)

tries :: q -> Tree q a -> Search q a ()
tries q ls = ContT $ \kont -> (q, ls) <: kont ()

tryMinimum :: q -> a -> Search q a ()
tryMinimum q a = yield q a >>= \case
   True -> done
   False -> pure ()
tryTransform :: q -> (b -> b) -> b -> Search q b b
tryTransform q f a = yield q a' >>= \case
   True -> pure a'
   False -> pure a
  where a' = f a

yield :: q -> a -> Search q a Bool
yield q a = ContT $ \contt -> (q, Tree a (contt True)) <: contt False
done :: Search q r a
done = ContT $ const (OrderedQueue [])

newtype OrderedQueue q a = OrderedQueue [(q,a)]
  deriving (Show, Eq, Functor)
instance Ord q => Semigroup (OrderedQueue q a) where
  OrderedQueue qa <> OrderedQueue qb = OrderedQueue (go qa qb)
    where
      go [] a = a
      go a [] = a
      go ls@((ql, vl): l) rs@((qr, vr):r) = case compare ql qr of
        GT -> (qr, vr) : go ls r
        _ -> (ql, vl) : go l rs
       
(<:) :: (q, a) -> OrderedQueue q a -> OrderedQueue q a
(<:) l (OrderedQueue qa) = OrderedQueue (l : qa)
type Search q r = ContT (Tree q r) (OrderedQueue q)
shrinkFrom :: a -> Search q a () -> Tree q a
shrinkFrom base c = Tree base (runContT c (const (OrderedQueue mempty)))

data Heap q a = NHeap (NHeap q a) | EmptyHeap
  deriving (Show, Eq, Functor)
instance Ord q => Semigroup (Heap q a) where
   EmptyHeap <> r = r
   r <> EmptyHeap = r
   NHeap l <> NHeap r = NHeap (merge2 l r)
instance Ord q => Monoid (Heap q a) where
   mempty = EmptyHeap
   mappend = (<>)
data NHeap q a = Heap { score :: q, val :: a, children :: [NHeap q a] }
  deriving (Show, Eq, Functor)
merge2 :: Ord q => NHeap q a -> NHeap q a -> NHeap q a
merge2 h1@(Heap q1 _ _) h2@(Heap q2 _ _)
  | q1 <= q2 = Heap q1 (val h1) (h2 : children h1)
  | otherwise = Heap q2 (val h2) (h1 : children h2)
pairUp :: Ord q => [NHeap q a] -> [NHeap q a]
pairUp [] = []
pairUp [h] = [h]
pairUp (h1:h2:hs) = merge2 h1 h2 : pairUp hs
merge :: Ord q => [NHeap q a] -> NHeap q a
merge ls =  Heap q r (pairUp (ls' <> children))
  where
    sel@(Heap q r children) = minimumBy (comparing score) ls
    ls' = deleteBy ((==) `on` score) sel ls

pop :: Ord q => NHeap q a -> (q, a, Heap q a)
pop (Heap q r []) = (q, r, EmptyHeap)
pop (Heap q r hs) = (q, r, NHeap (merge hs))
