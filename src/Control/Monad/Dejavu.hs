{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module Control.Monad.Dejavu (module Control.Monad.Dejavu)where

import Control.Monad.State
import Type.Reflection
import qualified Data.Text as T
import Control.Monad.Reader
import Data.Typeable (cast)
import GHC.Stack

data SomeVal = forall a. Show a => SomeVal { typeRep :: TypeRep a, value :: a }

instance Show SomeVal where
  show (SomeVal _ a) = "SomeVal" <> show a

data Tag = Named T.Text | None
  deriving (Eq, Ord, Show)
data Trace = Nil | Ctx Tag Trace | Leaf SomeVal | Node Trace Trace
  deriving Show
-- newtype LifeCycle = LifeCycle { onExit :: Trace }


newtype DejavuT m a = DejavuT { runDejavuT :: ReaderT (Maybe Trace) m (Trace, a) }
  deriving (Functor)
instance Applicative m => Applicative (DejavuT m) where
  pure a = DejavuT $ pure (Nil, a)
  (<*>) (DejavuT mf) (DejavuT ma) =
       DejavuT $ ReaderT $ \ctx ->
       let 
           (l,r) = case ctx of
               Just (Node ml mr) -> (Just ml, Just mr)
               _ -> (Nothing, Nothing)
       in c <$> runReaderT mf l <*> runReaderT ma r
     where
       c (t,f) (t',a) = (Node t t', f a)

instance Monad m => Monad (DejavuT m) where
  (>>=) (DejavuT m) g = DejavuT $ ReaderT $ \ctx -> do
      let 
           (l,r) = case ctx of
               Just (Node ml mr) -> (Just ml, Just mr)
               _ -> (Nothing, Nothing)
      (t, a) <- runReaderT m l
      let DejavuT m' = g a
      (t', b) <- runReaderT m' r
      pure (Node t t', b)
  (>>) = (*>)
  return = pure
instance MonadTrans DejavuT where
  lift :: Monad m => m a -> DejavuT m a
  lift = DejavuT . lift . fmap (Nil,)
instance MonadState s m => MonadState s (DejavuT m) where
  get :: DejavuT m s
  get = lift get
  put :: s -> DejavuT m ()
  put = lift . put

class Monad m => MonadDejavu m where
    putSlot :: (Show a, Typeable a) => a -> m ()
    getSlot :: Typeable a => m (Maybe a)
    child :: Tag -> m a -> m a
    localTrace :: (Maybe Trace -> Maybe Trace) -> m a -> m a

instance Monad m => MonadDejavu (DejavuT m) where
    localTrace f (DejavuT m) = DejavuT $ local f m
    putSlot :: (Show a, Typeable a) => a -> DejavuT m ()
    putSlot a = DejavuT $ ReaderT $ \_ -> pure (Leaf (SomeVal (typeOf a) a), ())
    getSlot = DejavuT $ ReaderT $ \r -> pure (Nil, r >>= \case
        Leaf (SomeVal TypeRep a) -> cast a
        _ -> Nothing)
    child tag m = DejavuT $ ReaderT $ \r -> do
        (t, a) <- runReaderT (runDejavuT m) (projTo r)
        pure (Ctx tag t, a)
      where
        projTo = \case
            Nothing -> Nothing
            Just (Ctx tag' t) | tag == tag' -> Just t
            _ -> Nothing

runMemo :: DejavuT m a -> Trace -> m (Trace, a)
runMemo (DejavuT m) t = runReaderT m (Just t)


newtype Memo a = Memo a
  deriving (Eq, Ord, Show, Typeable)

memo :: (Show a, MonadDejavu m, Typeable a) => m a -> m a
memo m = do
    ma <- getSlot
    a <- case ma of
        Just (Memo a) -> pure a
        Nothing -> m
    putSlot (Memo a)
    pure a

checkTrace :: (Eq a, MonadDejavu m, Typeable a) => a -> m r -> m r
checkTrace a m = do
    ma <- getSlot
    case ma of
        Just a' | a == a' -> m
        _ -> localTrace (const Nothing) m

callerLoc :: HasCallStack => SrcLoc
callerLoc = case getCallStack callStack of
    (_, loc):_ -> loc
    _ -> error "Unknown Sourceloc"
checkBranch :: (HasCallStack, MonadDejavu m) => m a -> m a
checkBranch = checkTrace (withFrozenCallStack callerLoc)
