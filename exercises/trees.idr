
module Main

||| A Binary Tree
data Tree elem = ||| An empty node with no children
                 Empty
               | ||| A node with a left subtree and a right subtree
                 Node (Tree elem) elem (Tree elem)

%name Tree tree1, tree2, tree3, tree4


insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x same@(Node left value right) = case compare x value  of
                                      LT => Node (insert x left) value right
                                      EQ => same
                                      GT => Node left value (insert x right)

listToTree : Ord elem => List elem -> Tree elem
listToTree = foldl (\tree, elem => insert elem tree) Empty

treeToList : Tree elem -> List elem
treeToList Empty = []
treeToList (Node tree1 x tree2) = let leftList = treeToList tree1 in
                                      leftList ++ x :: treeToList tree2


data Expr : Type -> Type where
     Literal : Num e => (value : e) -> Expr e
     Sum : Num e => (lhs : Expr e) -> (rhs : Expr e) -> Expr e
     Mult : Num e => (lhs : Expr e) -> (rhs : Expr e) -> Expr e
 --    Sub : Num e => (lhs : Expr e) -> (rhs : Expr e) -> Expr e
     
evaluate : Num e => Expr e -> e
evaluate (Literal value) = value
evaluate (Sum lhs rhs) = (evaluate lhs) + (evaluate rhs)
evaluate (Mult lhs rhs) = (evaluate lhs) * (evaluate rhs)
--evaluate (Sub lhs rhs) = (evaluate lhs) - (evaluate rhs)

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing y = y
maxMaybe left Nothing = left
maxMaybe (Just x) (Just y) = Just (max x y)
