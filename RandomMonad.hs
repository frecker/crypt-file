-- the RandomMonad - inspired by "Real World Haskell"
-- Frank Recker, 2012
module RandomMonad(RandomMonad,runRandomMonad,getRandomR,getRandom) where
import System.Random
import Control.Monad.State

type RandomMonad a = State StdGen a

runRandomMonad :: RandomMonad a -> IO a
runRandomMonad x = do
  g <- getStdGen
  let (x',g') = runState x g
  setStdGen g'
  return x'

getRandomR :: Random a => (a,a) -> RandomMonad a
getRandomR (u,o) =
  get >>= \gen -> do
  let (val,gen') = randomR (u,o) gen
  put gen'
  return val

getRandom :: Random a => RandomMonad a
getRandom =
  get >>= \gen -> do
  let (val,gen') = random gen
  put gen'
  return val
