module Shapes

export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export 
circle : Double -> Shape
circle = Circle

public export
data ShapeView : Shape -> Type where
  STriangle : (width : Double) -> (height : Double) -> ShapeView (triangle width height)
  SCircle : (radius : Double) -> ShapeView (circle radius)
  SRectangle : (width : Double) -> (height : Double) -> ShapeView (rectangle width height)


export
shapeView : (s : Shape) -> ShapeView s
shapeView (Triangle x y) = STriangle x y
shapeView (Rectangle x y) = SRectangle x y
shapeView (Circle x) = SCircle x

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

