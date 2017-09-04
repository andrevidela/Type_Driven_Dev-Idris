
data Access = LoggedOut | LoggedIn

data PwdCheck = Correct | Incorrect

PwdCheckState : PwdCheck -> Access
PwdCheckState Correct = LoggedIn
PwdCheckState Incorrect = LoggedOut

data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
  Password : String -> ShellCmd PwdCheck LoggedOut PwdCheckState

  Logout : ShellCmd () LoggedIn (const LoggedOut)

  GetSecret : ShellCmd String LoggedIn (const LoggedIn)

  PutStr : String -> ShellCmd () state (const state)

  Pure : (res : ty) -> ShellCmd ty (state_fn res) state_fn

  (>>=) : ShellCmd a s1 s2_fn ->
          ((res : a) -> ShellCmd b (s2_fn res) s3_fn) ->
          ShellCmd b s1 s3_fn

session : ShellCmd () LoggedOut (const LoggedOut)
session = do Correct <- Password "paasword"
               | Incorrect => PutStr "Wrong password"
             msg <- GetSecret
             PutStr ("Secret code : " ++ show msg ++ "\n")
             Logout

-- sessionBad : ShellCmd () LoggedOut (const LoggedOut)
-- sessionBad = do Password "paasword"
--                 msg <- GetSecret
--                 PutStr ("Secret Code: " ++ show msg ++ "\n")
--                 Logout

-- noLogout : ShellCmd () LoggedOut (const LoggedOut)
-- noLogout = do Correct <- Password "paasword"
--                 | Incorrect => PutStr "Wrong password"
--               msg <- GetSecret
--               PutStr ("Secret Code: " ++ show msg ++ "\n")
