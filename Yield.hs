-- Copied from: http://www.vex.net/~trebla/haskell/parsec-generally.xhtml

{-| Yield-style generators. -}
module Yield where

import Control.Monad.Cont
import Data.IORef

{-| 
Type of return values of generators. @More@ means the generator yields. @End@
means the generator finishes. See below for examples.
-}
data Dot a b = More a | End b deriving Show

{-|
Create a yield-style generator from a body. Example:

> g <- mkgen (\yield c0 -> do
>                c1 <- yield a0
>                c2 <- yield a1
>                return b
>            )

Then we can use:

> dot0 <- g c0  -- dot0 = More a0
> dot1 <- g c1  -- dot1 = More a1
> dot2 <- g c2  -- dot2 = End b

Further calls to @g@ return @End b@ too.

Although usually @m=n@, i.e., @g@ and the body are in the same monad as the
@mkgen@ call, technically they can be different. The @mkgen@ call
is in m with MonadIO for allocating IORef. The body and @g@ are in n with
MonadIO and MonadCont for using IORef and callCC.
-}
mkgen :: (MonadIO m, MonadIO n, MonadCont n) =>
         ((a -> n c) -> c -> n b) -> m (c -> n (Dot a b))
mkgen body = do
  inside <- liftIO (newIORef undefined)
  outside <- liftIO (newIORef undefined)
  let yield y = do
        o <- liftIO (readIORef outside)
        callCC (\ki -> do
                   liftIO (writeIORef inside ki)
                   o (More y)
               )
      next x = do
        i <- liftIO (readIORef inside)
        callCC (\ko -> do
                   liftIO (writeIORef outside ko)
                   i x
               )
      start x = do
        e <- body yield x
        liftIO (writeIORef inside (\_ -> return (End e)))
        o <- liftIO (readIORef outside)
        o (End e)
        undefined
  liftIO (writeIORef inside start)
  return next
