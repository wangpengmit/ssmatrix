{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, GADTs, UndecidableInstances, KindSignatures, ScopedTypeVariables, OverlappingInstances #-}

module Tag where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity

data T tag m a = T { runTag :: m a } deriving Show

instance Monad m => Monad (T tag m) where
   return a = T (return a)
   T x >>= f = T $ x >>= (runTag . f)

instance MonadTrans (T tag) where
   lift m = T m

class TWith t (m :: * -> *) (n :: * -> *) | t n -> m where
   taggedLift :: t -> m a -> n a

instance (Monad m, m ~ n) => TWith tag m (T tag n) where
   taggedLift _ x = lift x

instance (Monad m, Monad n, TWith tag m n, MonadTrans t) => TWith tag m (t n) where
   taggedLift tag x = lift (taggedLift tag x)

type TStateT tag s m = T tag (StateT s m)
runTStateT = runStateT . runTag

tput tag x = taggedLift tag (put x)
tget tag = taggedLift tag get

type TWriterT tag w m = T tag (WriterT w m)
runTWriterT = runWriterT . runTag

ttell tag x = taggedLift tag (tell x)

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
