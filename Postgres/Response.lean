import Socket
import Postgres.Util

open Socket
open Util
open List (foldr range)
open ByteArray
open Prod (fst snd)

structure Field where
  length : UInt32
  data : String

structure Column where
  colName: String
  tableOID: UInt32
  colIndex: UInt16
  typeOID: UInt32
  colLength: UInt16
  typeModifyer: UInt32
  format: UInt16

structure RowDescription where
  method : Char
  length : UInt32
  fieldCount : UInt16
  fields : List Column

structure DataRow where
  method : Char
  length : UInt32
  fieldCount : UInt16
  fields : List Field

structure Section where
  rowDesc : RowDescription
  dataRow : List DataRow

namespace QueryResponse

def parseColumn (bs : ByteArray) : Column × ByteArray :=
  let (colName, rest) := takeString bs
  let (tableOID, rest) := take4 rest
  let (colIndex, rest) := take2 rest
  let (typeOID, rest) := take4 rest
  let (colLength, rest) := take2 rest
  let (typeModifyer, rest) := take4 rest
  let (format, rest) := take2 rest
  (⟨
    colName,
    tableOID,
    colIndex,
    typeOID,
    colLength,
    typeModifyer,
    format
  ⟩, rest)

partial def parseColumns : UInt16 → Option (List Column) → ByteArray → List Column × ByteArray
  | 0, some xs, ba => (xs, ba)
  | n, none, ba => parseColumns (n-1) (some [fst $ parseColumn ba]) (snd $ parseColumn ba)
  | n, some xs, ba => parseColumns (n-1) (some $ xs.append [fst $ parseColumn ba]) (snd $ parseColumn ba)

def parseField (ba : ByteArray) : Field × ByteArray :=
  let (length, rest) := take4 ba
  let (content, rest) := takeNAsStr length.toNat rest
  (⟨length, content⟩, rest)

-- TODO: combine with parseColumns
partial def parseFields : UInt16 → Option (List Field) → ByteArray → List Field × ByteArray
  | 0, some xs, ba => (xs, ba)
  | n, none, ba => parseFields (n-1) (some [fst $ parseField ba]) (snd $ parseField ba)
  | n, some xs, ba => parseFields (n-1) (some $ xs.append [fst $ parseField ba]) (snd $ parseColumn ba)

partial def parseRows (socket : Socket) (l : List DataRow) : IO $ List DataRow := do
  let method := Char.ofNat (← socket.recv 1)[0].toNat
  if method != 'D' then
    return l
  let length := toUInt32LE (← socket.recv 4)
  let fieldCount := toUInt16LE $ ← socket.recv 2
  -- Excluding 6 Bytes for length and field count
  let content ← socket.recv (length - 6).toUSize
  let (fields, _) := parseFields fieldCount none content
  parseRows socket (l.append [⟨method, length, fieldCount, fields⟩])

def parseQueryResponse (socket : Socket) : IO Section := do
  let method := Char.ofNat (← socket.recv 1)[0].toNat
  let length := toUInt32LE $ ← socket.recv 4
  let fieldCount := toUInt16LE $ ← socket.recv 2
  -- Excluding 6 Bytes for length and field count
  let content ← socket.recv (length - 6).toUSize
  let (columns, _) := parseColumns fieldCount none content
  pure ⟨
    ⟨
      method,
      length,
      fieldCount,
      columns
    ⟩, (← parseRows socket [])
  ⟩

end QueryResponse
