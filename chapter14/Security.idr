-- exercises in "Type-Driven Development with Idris"
-- chapter 14, section 2, Security part

-- check that all functions are total
%default total

data Access = LoggedOut | LoggedIn
data PwdCheck = Correct | Incorrect

data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
  Password : String -> ShellCmd PwdCheck LoggedOut
                                         (\res => case res of
                                                    Correct => LoggedIn
                                                    Incorrect => LoggedOut)
  Logout : ShellCmd () LoggedIn (const LoggedOut)
  GetSecret : ShellCmd String LoggedIn (const LoggedIn)
  PutStr : String -> ShellCmd () state (const state)
  Pure : (res : ty) -> ShellCmd ty (state res) state
  (>>=) : ShellCmd a state1 state2 ->
          ((res : a) -> ShellCmd b (state2 res) state3) ->
          ShellCmd b state1 state3

session : ShellCmd () LoggedOut (const LoggedOut)
session = do Correct <- Password "wurzel"
             | Incorrect => PutStr "Wrong password"
             msg <- GetSecret
             PutStr ("Secret code: " ++ show msg ++ "\n")
             Logout

-- sessionBad : ShellCmd () LoggedOut (const LoggedOut)
-- sessionBad = do Password "wurzel"
--                 msg <- GetSecret
--                 PutStr ("Secret code: " ++ show msg ++ "\n")
--                 Logout

-- noLogout : ShellCmd () LoggedOut (const LoggedOut)
-- noLogout = do Correct <- Password "wurzel"
--               | Incorrect => PutStr "Wrong password"
--               msg <- GetSecret
--               PutStr ("Secret code: " ++ show msg ++ "\n")
