-- exercises in "Type-Driven Development with Idris"
-- chapter 10

import Shape

-- check that all functions are total
%default total

area : Shape -> Double
area x with (shapeView x)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius
