import datastore
import shapes
import Data.Vect

-- getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
-- getValues input with (storeView input)
--   getValues input | SNil = []
--   getValues (addToStore value store) | (SAdd rec) = ?getValues_rhs_2

filterKeys : (test : SchemaType val_schema -> Bool) ->
             DataStore (SString .+. val_schema) -> List String
filterKeys test input with (storeView input)
    filterKeys test empty | SNil = []
    filterKeys test (addToStore (key, value) store) | (SAdd rec)
               = if test value
                    then key :: filterKeys test store | rec
                    else filterKeys test store | rec

myarea : Shape -> Double
myarea x with (shapeView x)
  area (triangle width height) | (STriangle width height) = width * height / 2
  area (circle radius) | (SCircle radius) = radius * pi
  area (rectangle width height) | (SRectangle width height) = width * height

