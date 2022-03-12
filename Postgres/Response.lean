/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Socket
import Postgres.Util

open Socket
open Util
open List (map foldr range)
open ByteArray
open Prod (fst snd)

structure Field where
  length : UInt32
  data : String

instance : ToString Field where
  toString s := s.data

structure Column where
  colName: String
  tableOID: UInt32
  colIndex: UInt16
  typeOID: UInt32
  colLength: UInt16
  typeModifyer: UInt32
  format: UInt16

instance : ToString Column where
  toString c := c.colName

structure RowDescription where
  method : Char
  length : UInt32
  columnCount : UInt16
  columns : List Column

instance : ToString RowDescription where
  toString rd := " × ".intercalate (map toString rd.columns)

structure DataRow where
  method : Char
  length : UInt32
  fieldCount : UInt16
  fields : List Field

instance : ToString DataRow where
  toString dr := "(" ++ ", ".intercalate (map toString dr.fields) ++ ")"

structure Section where
  rowDesc : RowDescription
  dataRow : List DataRow

instance : ToString Section where
  toString s := s!"{s.rowDesc}\n" ++ "\n".intercalate (map toString s.dataRow)

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

/--
  Parses `n` elements `α` recursively with the given parse function `parseα`
-/
partial def parse {α : Type u} : UInt16 → Option (List α) → (ByteArray → α × ByteArray) → ByteArray → List α × ByteArray
  | 0, some xs, _, ba => (xs, ba)
  | n, none, parseα, ba => parse (n-1) (some [fst $ parseα ba]) parseα (snd $ parseα ba)
  | n, some xs, parseα, ba => parse (n-1) (some $ xs.append [fst $ parseα ba]) parseα (snd $ parseα ba)

def parseField (ba : ByteArray) : Field × ByteArray :=
  let (length, rest) := take4 ba
  let (content, rest) := takeNAsStr length.toNat rest
  (⟨length, content⟩, rest)

partial def parseRows (socket : Socket) (l : List DataRow) : IO $ List DataRow := do
  let method := Char.ofNat (← socket.recv 1)[0].toNat
  if method != 'D' then
    return l
  let length := toUInt32LE (← socket.recv 4)
  let fieldCount := toUInt16LE $ ← socket.recv 2
  -- Excluding 6 Bytes for length and field count
  let content ← socket.recv (length - 6).toUSize
  let (fields, _) := parse fieldCount none parseField content
  parseRows socket (l.append [⟨method, length, fieldCount, fields⟩])

def parseQueryResponse (socket : Socket) : IO Section := do
  let method := Char.ofNat (← socket.recv 1)[0].toNat
  let length := toUInt32LE $ ← socket.recv 4
  let fieldCount := toUInt16LE $ ← socket.recv 2
  -- Excluding 6 Bytes for length and field count
  let content ← socket.recv (length - 6).toUSize
  let (columns, _) := parse fieldCount none parseColumn content
  pure ⟨
    ⟨
      method,
      length,
      fieldCount,
      columns
    ⟩,
    (← parseRows socket [])
  ⟩

end QueryResponse
