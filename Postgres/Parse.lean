import Postgres

namespace Parse

inductive ParseByteArray (α : Type) where
  | success (ba : ByteArray) (rest : α)
  | error (ba : ByteArray) (err : String)

end Parse

def Parse (α : Type) : Type := ByteArray → Parse.ParseByteArray α

namespace Parse

open ParseByteArray Util QueryResponse

instance (α : Type) : Inhabited (Parse α) :=
  ⟨λ ba => error ba ""⟩

def pure (a : α) : Parse α := λ ba =>
  success ba a

def bind {α β : Type} (f : Parse α) (g : α → Parse β) : Parse β := λ ba =>
  match f ba with
  | success rest a => g a rest
  | error pos msg => error pos msg

instance : Monad Parse :=
  { pure := Parse.pure, bind }

def fail (msg : String) : Parse α := λ ba =>
  error ba msg

def orElse (p : Parse α) (q : Unit → Parse α) : Parse α := λ ba =>
  match p ba with
  | success rest a => success rest a
  | error rest err =>
    if ba.size = rest.size then q () ba else error rest err

@[inline]
def attempt (p : Parse α) : Parse α := λ ba =>
  match p ba with
  | success rem res => success rem res
  | error _ err => error ba err

instance : Alternative Parse :=
  ⟨fail "", orElse⟩

def expectedEndOfInput := "expected end of input"

def eof : Parse Unit := λ ba =>
  if ba.isEmpty then
    error ba expectedEndOfInput
  else
    success ba ()

def string (s : String := "") : Parse String := λ ba =>
  let (str, rest) := takeString ba ""
  if str = "" then
    error ba "No String could be parsed"
  else
    success rest str

def twoBytes : Parse UInt16 := λ ba =>
  if ba.size > 1 then
    let (i, rest) := take2 ba
    success rest i
  else
    error ba "No UInt16 could be parsed"

def fourBytes : Parse UInt32 := λ ba =>
  if ba.size > 1 then
    let (i, rest) := take4 ba
    success rest i
  else
    error ba "No UInt32 could be parsed"

def column : Parse Column := do
  pure ⟨
    ← string,
    ← fourBytes,
    ← twoBytes,
    ← fourBytes,
    ← twoBytes,
    ← fourBytes,
    ← twoBytes
  ⟩

end Parse
