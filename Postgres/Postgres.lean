import Socket

open Socket
open AddressFamily
open SockType
open List (map foldr)
open ByteArray (size mkEmpty)
open String (singleton)

def foldByteArray (xs : List ByteArray) : ByteArray :=
  foldr ByteArray.append (mkEmpty 0) xs

def uInt16ToByteArray (i: UInt16) : ByteArray :=
  List.toByteArray $ map (UInt16.toUInt8 ∘ i.shiftRight ∘ (. * 8)) [1, 0]

def uInt32ToByteArray (i: UInt32) : ByteArray :=
  List.toByteArray $ map (UInt32.toUInt8 ∘ i.shiftRight ∘ (. * 8)) [3, 2, 1, 0]

def toUInt32LE (bs : ByteArray) : UInt32 :=
  (bs.get! 0).toUInt32 <<< 0x18 |||
  (bs.get! 1).toUInt32 <<< 0x10 |||
  (bs.get! 2).toUInt32 <<< 0x8  |||
  (bs.get! 3).toUInt32

namespace Connect

class ToByteArray (α : Type u) where
  toByteArray : α → ByteArray

export ToByteArray (toByteArray)

structure RegularMessage where
  method: Char
  data: String

instance : ToByteArray RegularMessage where
  toByteArray msg :=
    let pstfx := ByteArray.mk $ mkArray 1 0
    let method := msg.method.toString.toUTF8
    let data := msg.data.toUTF8
    -- 5 Bytes for method + length
    let length := uInt32ToByteArray ∘ Nat.toUInt32 $ 5 + size data
    foldByteArray [method, length, data, pstfx]

structure StartUpMessage where
  majorVersion: UInt16
  minorVersion: UInt16
  user: String
  database: String
  applicationName: String
  clientEncoding: String

instance : ToByteArray StartUpMessage where
  toByteArray msg :=
    let pstfix := ByteArray.mk $ mkArray 2 0
    let majorVersion := uInt16ToByteArray msg.majorVersion
    let minorVersion := uInt16ToByteArray msg.minorVersion
    let data := String.toUTF8 $ (singleton '\x00').intercalate [
      "user", s!"{msg.user}",
      "database", s!"{msg.database}",
      "application_name", s!"{msg.applicationName}",
      "client_encoding", s!"{msg.clientEncoding}"
    ]
    -- 10 Bytes for postfix + major/minor Version + length
    let length := uInt32ToByteArray ∘ Nat.toUInt32 $ 10 + size data
    foldByteArray [length, majorVersion, minorVersion, data, pstfix]

inductive PSQLMessage where
  | startUpMessage : StartUpMessage → PSQLMessage
  | regularMessage : RegularMessage → PSQLMessage

instance : ToByteArray PSQLMessage where
  toByteArray
    | PSQLMessage.startUpMessage m => toByteArray m
    | PSQLMessage.regularMessage m => toByteArray m

def sendMessage (socket : Socket) (msg : PSQLMessage) : IO (Char × ByteArray) := do
  let req ← socket.send $ toByteArray $ msg
  let res ← socket.recv 5
  let flag := Char.ofNat $ ((res.extract 0 1).get! 0).toNat
  let size := toUInt32LE $ res.extract 1 5
  let data ← socket.recv (size.toUSize - 5)
  pure (flag, data)

def sendStartupMessage (socket : Socket) (user : String) (database : String) : IO (Char × ByteArray) := do
  let msg := PSQLMessage.startUpMessage ⟨3 ,0 ,user ,database, "lean", "UTF8"⟩
  sendMessage socket msg

-- TODO: Additionally support SHA256 and MD5 authentication
def sendPassword (socket : Socket) (password : String) : IO (Char × ByteArray) := do
  let msg := PSQLMessage.regularMessage ⟨'p', password⟩
  sendMessage socket msg

def openConnection (host : String) (port : String) (user : String) (database : String) (password : String) : IO Socket := do
  let dataSource ← SockAddr.mk host port inet stream
  let socket ← Socket.mk inet stream
  socket.connect dataSource
  let startUpRes ← sendStartupMessage socket user database
  if startUpRes.fst != 'R' then
    throw $ IO.Error.userError "Database connection failed"
 
  -- TODO: Clear buffer properly
  let _ ← socket.recv 1000
  let sendPWRes ← sendPassword socket password
  if sendPWRes.fst != 'R' || toUInt32LE sendPWRes.snd != 0 then
    throw $ IO.Error.userError "Password authentication failed"
  let _ ← socket.recv 1000
  pure socket

end Connect
