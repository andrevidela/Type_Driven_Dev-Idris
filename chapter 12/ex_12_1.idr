
import Control.Monad.State

data Tree a = Empty | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty
                            "Jim"
                            Empty)
                      "Fred"
                      (Node Empty 
                            "Shella"
                            Empty))
                 "Alice"
                 (Node Empty 
                       "Bob" 
                       (Node Empty 
                             "Eve"
                             Empty))

update : (stateType -> stateType) -> State stateType ()
update f = do current <- get
              put (f current)

increase : Nat -> State Nat ()
increase x = update (+x)

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node left val right) = do left_label <- treeLabelWith left -- label the left subtree
                                         (this :: rest) <- get -- get the local state
                                         put rest -- change local state
                                         right_label <- treeLabelWith right
                                         pure $ Node left_label (this, val) right_label

countEmpty : Tree a -> State Nat ()
countEmpty Empty = update (+1)
countEmpty (Node left elem right) = do countEmpty left
                                       countEmpty right

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = update (\t => (fst t + 1, snd t))
countEmptyNode (Node left elem right) = do countEmptyNode left
                                           countEmptyNode right
                                           (empties, nodes) <- get
                                           put (empties, nodes + 1)
                                           
