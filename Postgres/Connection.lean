import Socket

open Socket
open AddressFamily
open SockType
open List (map foldr)
open ByteArray (size mkEmpty)
open UInt32 (toUInt8)

namespace Connection

class ToByteArray (α : Type u) where
  toByteArray : α → ByteArray

export ToByteArray (toByteArray)

def foldByteArray (xs : List ByteArray) : ByteArray :=
  foldr ByteArray.append (mkEmpty 0) xs

def natTo4ByteArray (n: Nat) : ByteArray :=
  List.toByteArray $ map (toUInt8 ∘ n.toUInt32.shiftRight) [24, 16, 8, 0]

def toUInt32LE (bs : ByteArray) : UInt32 :=
  (bs.get! 0).toUInt32 <<< 0x18 |||
  (bs.get! 1).toUInt32 <<< 0x10 |||
  (bs.get! 2).toUInt32 <<< 0x8  |||
  (bs.get! 3).toUInt32

def natTo2ByteArray (n: Nat) : ByteArray :=
  List.toByteArray $ map (toUInt8 ∘ n.toUInt32.shiftRight) [8, 0]

structure RegularMessage where
  method: Char
  data: String

instance : ToByteArray RegularMessage where
  toByteArray msg :=
    let pstfx := ByteArray.mk $ mkArray 1 0
    let method := msg.method.toString.toUTF8
    let data := msg.data.toUTF8
    -- The size of length must be included therefore adding 4 Bytes for UInt32
    let length := natTo4ByteArray $ 4 + (size $ foldByteArray [method, data])
    foldByteArray [method, length, data, pstfx]

structure StartUpMessage where
  majorVersion: Nat
  minorVersion: Nat
  user: String
  database: String
  applicationName: String := "lean"
  clientEncoding: String := "UTF8"
  deriving Inhabited

instance : ToByteArray StartUpMessage where
  toByteArray msg :=
    let delim := ByteArray.mk $ mkArray 1 0
    let pstfix := ByteArray.mk $ mkArray 2 0
    let majorVersion := natTo2ByteArray msg.majorVersion
    let minorVersion := natTo2ByteArray msg.minorVersion
    -- TODO: Find better way to build zero-Byte separated ByteArray for database Information
    let user := "user".toUTF8 ++ delim ++ msg.user.toUTF8 ++ delim
    let database := "database".toUTF8 ++ delim ++ msg.database.toUTF8 ++ delim
    let applicationName := "application_name".toUTF8 ++ delim ++ msg.applicationName.toUTF8 ++ delim
    let clientEncoding := "client_encoding".toUTF8 ++ delim ++ msg.clientEncoding.toUTF8
    -- The size of length must be included therefore adding 4 Bytes for UInt32
    let length := natTo4ByteArray $ 4 + (size $ foldByteArray [majorVersion, minorVersion, user, database, applicationName, clientEncoding, pstfix])
    foldByteArray [length, majorVersion, minorVersion, user, database, applicationName, clientEncoding, pstfix]

inductive PSQLMessage where
  | startUpMessage (message : StartUpMessage) : PSQLMessage
  | regularMessage (message : RegularMessage) : PSQLMessage

instance : ToByteArray PSQLMessage where
  toByteArray msg := 
  match msg with
  | PSQLMessage.startUpMessage x => toByteArray x
  | PSQLMessage.regularMessage x  => toByteArray x

def sendMessage (socket : Socket) (msg : PSQLMessage) : IO (Char × ByteArray) := do
  let req ← socket.send $ toByteArray $ msg
  let res ← socket.recv 5
  let flag := Char.ofNat $ ((res.extract 0 1).get! 0).toNat
  let size := toUInt32LE $ res.extract 1 5
  let data ← socket.recv (size.toUSize - 5)
  pure (flag, data)

def sendStartupMessage (socket : Socket) (user : String) (database : String) : IO (Char × ByteArray) := do
  let msg := PSQLMessage.startUpMessage $ StartUpMessage.mk 3 0 user database "lean" "UTF8"
  sendMessage socket msg

-- TODO: Additionally support SHA256 and MD5 authentication
def sendPassword (socket : Socket) (password : String) : IO (Char × ByteArray) := do
  let msg := PSQLMessage.regularMessage $ RegularMessage.mk 'p' password
  sendMessage socket msg

def openConnection (host : String) (port : String) (user : String) (database : String) (password : String) : IO Socket := do
  let dataSource ← SockAddr.mk ⟨
    host,
    port,
    inet,
    stream
  ⟩
  let socket ← Socket.mk inet stream
  socket.connect dataSource
  let startUpRes ← sendStartupMessage socket user database
  if startUpRes.fst != 'R' then
    IO.eprintln "Database connection failed."
  
  -- TODO: Clear buffer properly
  let _ ← socket.recv 1000
  let sendPWRes ← sendPassword socket password
  if sendPWRes.fst != 'R' || toUInt32LE sendPWRes.snd != 0 then
    IO.eprintln "Password authentication failed"
  let _ ← socket.recv 1000
  pure socket

end Connection
