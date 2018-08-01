-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 10, Shapes
-- this is only for the Shapes in chapter 10, for other chapters see the chapterXX.idr files

module Shapes10

-- check that all functions are total
%default total

export data Shape = Triangle Double Double
                  | Rectangle Double Double
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
  STriangle : ShapeView (triangle base height)
  SRectangle : ShapeView (rectangle width height)
  SCircle : ShapeView (circle radius)

export
shapeView : (s : Shape) -> ShapeView s
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle
