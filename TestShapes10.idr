-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 10, Shapes (Tests)
-- this is only for the Shapes in chapter 10, for other chapters see the chapterXX.idr files

import Shapes10

-- check that all functions are total
%default total

area : Shape -> Double
area x with (shapeView x)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius
