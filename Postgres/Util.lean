/-
  Copyright (c) 2022 Florian Würmseer. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Florian Würmseer
-/

open List (map foldr toByteArray)
open ByteArray (mkEmpty append extract)
open String (fromUTF8Unchecked)

namespace Util

def foldByteArray (xs : List ByteArray) : ByteArray :=
  foldr append (mkEmpty 0) xs

def uInt16ToByteArray (i: UInt16) : ByteArray :=
  toByteArray $ map (UInt16.toUInt8 ∘ i.shiftRight ∘ (. * 8)) [1, 0]

def uInt32ToByteArray (i: UInt32) : ByteArray :=
  toByteArray $ map (UInt32.toUInt8 ∘ i.shiftRight ∘ (. * 8)) [3, 2, 1, 0]

def toUInt32LE (bs : ByteArray) : UInt32 :=
  (bs.get! 0).toUInt32 <<< 0x18 |||
  (bs.get! 1).toUInt32 <<< 0x10 |||
  (bs.get! 2).toUInt32 <<< 0x8  |||
  (bs.get! 3).toUInt32

def toUInt16LE (bs : ByteArray) : UInt16 :=
  (bs.get! 0).toUInt16 <<< 0x18 |||
  (bs.get! 1).toUInt16 <<< 0x10

def take2 (ba : ByteArray) : UInt16 × ByteArray :=
  (toUInt16LE (extract ba 0 2), extract ba 2 ba.size)

def take4 (ba : ByteArray) : UInt32 × ByteArray :=
  (toUInt32LE (extract ba 0 4), extract ba 4 ba.size)

partial def takeString (ba : ByteArray) (string : String := "") : String × ByteArray :=
  match ba.size with
    | 0 => (string, mkEmpty 0)
    | 1 => (string ++ fromUTF8Unchecked ba, mkEmpty 0)
    | _ =>  match ba[0] with
      | 0 => (string, extract ba 1 ba.size)
      | x => takeString (extract ba 1 ba.size) (string ++ (fromUTF8Unchecked $ extract ba 0 1))

def takeNAsStr (n : Nat) (ba : ByteArray) : String × ByteArray :=
  (fromUTF8Unchecked (extract ba 0 n), extract ba n ba.size)

end Util
