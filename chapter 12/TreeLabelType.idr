
data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : stateType -> State stateType ()

  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

get : State stateType stateType
get = Get

put : stateType -> State stateType ()
put = Put

pure : ty -> State stateType ty
pure = Pure

(>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
(>>=) = Bind

runState : State stateType a -> (st : stateType) -> (a, stateType)
runState Get st = (st, st)
runState (Put newState) st = ((), newState)
runState (Pure x) st = (x, st)
runState (Bind cmd prog) st = let (val, nextState) = runState cmd st in
                                  runState (prog val) nextState

data Tree a = Empty | Node (Tree a) a (Tree a)

flatten : Tree a -> List a
flatten Empty = []
flatten (Node left elem right) = (flatten left) ++ [elem] ++ (flatten right)

testTree : Tree String
testTree = (Node (Node Empty "b" Empty) "a" (Node (Node Empty "d" Empty) "c" (Node Empty "e" (Node Empty "f" Empty))))

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = Pure Empty
treeLabelWith (Node left elem right) 
  = do left_label <- treeLabelWith left
       (label :: rest) <- get
       put rest
       right_label <- treeLabelWith right
       pure $ Node left_label (label, elem) right_label

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = fst $ runState (treeLabelWith tree) [1..]

Functor (State stateType) where
  map func x = Bind x (Pure . func)

Applicative (State stateType) where
  pure = Pure
  (<*>) f a = Bind f (\f' =>
              Bind a (\a' =>
              Pure (f' a')))
Monad (State stateType) where
  (>>=) = Bind


addIfPositive : Integer -> State Integer Bool
addIfPositive val = do when (val > 0) $ 
                             do current <- get
                                put (current + val)
                       pure (val > 0)

addPositive : List Integer -> State Integer Nat
addPositive vals = do added <- traverse addIfPositive vals
                      pure (length (filter id added))
