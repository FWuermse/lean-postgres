/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

import Socket
import Postgres.Util
import Postgres.Parse

open Socket
open Util
open Parse
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

def column : Parse Column := do
  Parse.pure ⟨
    ← string,
    ← fourBytes,
    ← twoBytes,
    ← fourBytes,
    ← twoBytes,
    ← fourBytes,
    ← twoBytes
  ⟩

/--
  Parses `n` elements `α` recursively with the given parser
-/
partial def parse {α : Type} : UInt16 → Option (List α) → Parse α → Parse (List α)
  | 0, some xs, _ => do Parse.pure xs
  | n, none, p => do parse (n-1) (some [← p]) p
  | n, some xs, p => do parse (n-1) (some $ xs.append [← p]) p

def parseField (ba : ByteArray) : Field × ByteArray :=
  let (length, rest) := take4 ba
  let (content, rest) := takeNAsStr length.toNat rest
  (⟨length, content⟩, rest)

def field : Parse Field := do
  let length ← fourBytes
  Parse.pure ⟨
    length,
    ← nBytes length.toNat
  ⟩

partial def parseRows (socket : Socket) (l : List DataRow) : IO $ List DataRow := do
  let method := Char.ofNat (← socket.recv 1)[0].toNat
  if method != 'D' then
    return l
  let length := toUInt32LE (← socket.recv 4)
  let fieldCount := toUInt16LE $ ← socket.recv 2
  -- Excluding 6 Bytes for length and field count
  let content ← socket.recv (length - 6).toUSize
  let pfields := parse fieldCount none field
  let fields := match pfields content with
    | Parse.ParseByteArray.success ba xs => xs
    | Parse.ParseByteArray.error ba s => []
  parseRows socket (l.append [⟨method, length, fieldCount, fields⟩])

def parseQueryResponse (socket : Socket) : IO Section := do
  let method := Char.ofNat (← socket.recv 1)[0].toNat
  let length := toUInt32LE $ ← socket.recv 4
  let fieldCount := toUInt16LE $ ← socket.recv 2
  -- Excluding 6 Bytes for length and field count
  let content ← socket.recv (length - 6).toUSize
  let pcolumns := parse fieldCount none column
  let columns := match pcolumns content with
    | Parse.ParseByteArray.success ba xs => xs
    | Parse.ParseByteArray.error ba s => []
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
