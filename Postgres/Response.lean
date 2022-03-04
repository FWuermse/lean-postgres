class FromByteArray (α : Type u) where
  fromByteArray? : Section → Except String α

export FromByteArray (fromByteArray?)

structure Column where
  length : UInt32
  data : String

structure RowDescription where
  method : Char
  length : UInt32
  fieldCount : UInt16
  fields : List String

inductive DataRow where
  | none
  | some : Char → UInt32 → UInt16 → List Column → DataRow → DataRow

inductive Section where
  | rowDesc : RowDescription → Section
  | dataRow : DataRow → Section
