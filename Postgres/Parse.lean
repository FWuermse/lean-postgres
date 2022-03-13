import Postgres.Util

namespace Parse

inductive ParseByteArray (α : Type) where
  | success (ba : ByteArray) (res : α)
  | error (ba : ByteArray) (err : String)

end Parse

def Parse (α : Type) : Type := ByteArray → Parse.ParseByteArray α

namespace Parse

open ParseByteArray Util

instance (α : Type) : Inhabited (Parse α) :=
  ⟨λ ba => error ba ""⟩

def pure (a : α) : Parse α := λ ba =>
  success ba a

def bind {α β : Type} (f : Parse α) (g : α → Parse β) : Parse β := λ ba =>
  match f ba with
  | success res a => g a res
  | error pos msg => error pos msg

instance : Monad Parse :=
  { pure := Parse.pure, bind }

def fail (msg : String) : Parse α := λ ba =>
  error ba msg

def orElse (p : Parse α) (q : Unit → Parse α) : Parse α := λ ba =>
  match p ba with
  | success res a => success res a
  | error res err =>
    if ba.size = res.size then q () ba else error res err

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
  let (str, res) := takeString ba ""
  if str = "" then
    error ba "No String could be parsed"
  else
    success res str

def twoBytes : Parse UInt16 := λ ba =>
  if ba.size > 1 then
    let (i, res) := take2 ba
    success res i
  else
    error ba "No UInt16 could be parsed"

def fourBytes : Parse UInt32 := λ ba =>
  if ba.size > 1 then
    let (i, res) := take4 ba
    success res i
  else
    error ba "No UInt32 could be parsed"

def nBytes (n : Nat) : Parse String := λ ba =>
  let (str, res) := takeNAsStr n ba
  if str = "" then
    error ba s!"No String with {n} bytes could be parsed"
  else
    success res str

end Parse
