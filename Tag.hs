-- Tagged monad transformer stack
-- Adapted from http://blog.sigfpe.com/2010/02/tagging-monad-transformer-layers.html

{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, GADTs, UndecidableInstances, KindSignatures, OverlappingInstances #-}

module Tag where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity

data TagT tag m a = TagT { runTag :: m a } deriving Show

instance Monad m => Monad (TagT tag m) where
   return a = TagT (return a)
   TagT x >>= f = TagT $ x >>= (runTag . f)

instance MonadTrans (TagT tag) where
   lift m = TagT m

instance Functor m => Functor (TagT tag m) where
  fmap f = TagT . fmap f . runTag

-- monad transformer stack n contains monad m with tag t
class Contains (m :: * -> *) t (n :: * -> *) | m t -> n where
   liftFrom :: t -> n a -> m a

instance (Monad m, m ~ n) => Contains (TagT tag m) tag n where
   liftFrom _ x = lift x

instance (MonadTrans t, Monad m, Contains m tag n) => Contains (t m) tag n where
   liftFrom tag x = lift (liftFrom tag x)

type TStateT tag s m = TagT tag (StateT s m)
runTStateT = runStateT . runTag

tput tag x = liftFrom tag (put x)
tget tag = liftFrom tag get

type TState tag s = TStateT tag s Identity
runTState m = runIdentity . runTStateT m

type TWriterT tag w m = TagT tag (WriterT w m)
runTWriterT = runWriterT . runTag

ttell tag x = liftFrom tag (tell x)

type TWriter tag w = TWriterT tag w Identity
runTWriter = runIdentity . runTWriterT

-- tests

test1 :: StateT Int (StateT Int (StateT Int (WriterT String Identity))) Int
test1 = do
   put 1
   lift $ put 2
   lift $ lift $ put 3
   a <- get
   b <- lift $ get
   c <- lift $ lift $ get
   lift $ lift $ lift $ tell $ show $ a+b+c
   return $ a*b*c

go1 = runIdentity (runWriterT (runStateT (runStateT (runStateT test1 0) 0) 0))

data A = A
data B = B
data C = C
data D = D

test2 :: TStateT A Int (TStateT B Int (TStateT C Int (TWriterT D String Identity))) Int

test2 = do
   tput A 1
   tput B 2
   tput C 3
   a <- tget A
   b <- tget B
   c <- tget C
   ttell D $ show $ a+b+c
   return $ a*b*c

go2 = runIdentity (runTWriterT (runTStateT (runTStateT (runTStateT test2 0) 0) 0))
