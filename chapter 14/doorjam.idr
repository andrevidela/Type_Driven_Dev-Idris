

data DoorState = DoorOpen | DoorClosed
data DoorResult = OK | Jammed

StateResult : DoorResult -> DoorState
StateResult OK = DoorOpen
StateResult Jammed = DoorClosed

data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
  Open : DoorCmd DoorResult DoorClosed StateResult
  RingBell : DoorCmd () DoorClosed (const DoorClosed)
  Close : DoorCmd () DoorOpen (const DoorClosed)
  Display : String -> DoorCmd () state (const state)
  Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn
  (>>=) : DoorCmd a s1 s2_fn ->
          ((res : a) -> DoorCmd b (s2_fn res) s3_fn) ->
          DoorCmd b s1 s3_fn

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              OK <- Open | Jammed => Display "Door jammed"
              Display "Door opened"
              Close
