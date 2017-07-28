
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where
  (==) (Triangle al bl) (Triangle ar br) = al == ar && bl == br
  (==) (Rectangle al bl) (Rectangle ar br) = al == ar && bl == br
  (==) (Circle x) (Circle y) = x == y
  (==) _ _ = False


area : Shape -> Double
area (Triangle x y) = x * y / 2
area (Rectangle x y) = x * y
area (Circle r) = pi * r * r

Ord Shape where
  compare lhs rhs = compare (area lhs) (area rhs)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4,
              Rectangle 2 7]

