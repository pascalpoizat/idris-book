-- exercises in "Type-Driven Development with Idris" Edit
-- chapter 11, section 3, questions 2 and 3

-- check that all functions are total
%default total

data LazyFuel = LDry | LMore (Lazy LazyFuel)

partial
forever : LazyFuel
forever = LMore forever

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b
  ReadFile : String -> Command (Either FileError String)
  WriteFile : String -> String -> Command (Either FileError ())

namespace Command
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do res <- runCommand x
                           runCommand (f res)
runCommand (ReadFile f) = readFile f
runCommand (WriteFile f x) = writeFile f x

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace Console
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

run : LazyFuel -> ConsoleIO a -> IO (Maybe a)
run _ (Quit v) = pure $ Just v
run LDry (Do act gen) = pure Nothing
run (LMore fuel) (Do act gen) = do res <- runCommand act
                                   run fuel $ gen res

data ShellInput = Cat String
                | Copy String String
                | Exit
                | Error String

readInput : (prompt : String) -> Command ShellInput
readInput prompt
  = do PutStr prompt
       input <- GetLine
       parts <- Pure $ words input
       case parts of
         ["cat", filename] => Pure $ Cat filename
         ["copy", source, destination] => Pure $ Copy source destination
         ["exit"] => Pure $ Exit
         _ => Pure $ Error "Unknown command\n"

cat : String -> Command ()
cat filename = do res <- ReadFile filename
                  case res of
                    Right contents => PutStr contents
                    Left error => PutStr $ show error ++ "\n"

copy : String -> String -> Command ()
copy source destination =
  do res1 <- ReadFile source
     case res1 of
       Left error => PutStr $ show error ++ " (source) \n"
       Right contents => do res2 <- WriteFile destination contents
                            case res2 of
                              Left error => PutStr $ show error ++ " (destination)\n"
                              Right () => PutStr "File copied\n"

shell : ConsoleIO ()
shell = do cmd <- readInput "> "
           case cmd of
             Cat filename => do cat filename
                                shell
             Copy source destination => do copy source destination
                                           shell
             Exit => Quit ()
             Error error => do PutStr error
                               shell

-- :exec
-- > cat input.txt
-- (...) file
-- > copy input.txt output.txt
-- File copied
-- > cat output.txt
-- (...) file
partial
main : IO ()
main = do run forever shell
          pure ()
