-- exercises in "Type-Driven Development with Idris"
-- chapter 6

-- check that all functions are total
%default total

data Format = Number Format
            | Doubble Format
            | Str Format
            | Chhar Format
            | Lit String Format
            | End
%name Format fmt, fmt1, fmt2, fmt3

PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Doubble fmt) = (d : Double) -> PrintfType fmt
PrintfType (Str fmt) = (str : String) -> PrintfType fmt
PrintfType (Chhar fmt) = (car : Char) -> PrintfType fmt
PrintfType (Lit str fmt) = PrintfType fmt
PrintfType End = String

printFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printFmt (Number fmt) acc = \i => printFmt fmt (acc ++ show i)
printFmt (Doubble fmt) acc = \d => printFmt fmt (acc ++ show d)
printFmt (Str fmt) acc = \str => printFmt fmt (acc ++ str)
printFmt (Chhar fmt) acc = \char => printFmt fmt (acc ++ show char)
printFmt (Lit str fmt) acc = printFmt fmt (acc ++ str)
printFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Doubble (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chhar (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                          Lit str chars' => Lit (strCons c str) chars'
                          fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printFmt _ ""
-- > :t printf "%s = %d"
-- printf "%s = %d" : String -> Int -> String
-- > :t printf "%c %f"
-- printf "%c %f" : Char -> Double -> String
-- > printf "%c %f" 'X' 24
-- "'X' 24.0" : String
