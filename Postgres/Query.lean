import Socket
import Postgres.Connection

open Socket
open Connection

-- TODO: define inductive type to handle queries and query-responses

def sendQuery (socket : Socket) (query : String) : IO ByteArray := do
  let req ← socket.send $ toByteArray $ RegularMessage.mk 'Q' query
  let x ← socket.recv 5
  pure $ ← socket.recv 1000