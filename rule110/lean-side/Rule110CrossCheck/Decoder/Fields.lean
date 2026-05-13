import Rule110CrossCheck.Decoder.Core

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.FKernel.Package
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

namespace BEDC.Rule110CrossCheck

def fieldValue? (fields : List (String × String)) (key : String) : Option String :=
  match fields with
  | [] => none
  | (k, v) :: rest => if k = key then some v else fieldValue? rest key

def fieldAtom (value : String) : String :=
  match (trim value).splitOn " " with
  | atom :: _ => atom
  | [] => ""

def fieldValueAny? (fields : List (String × String)) (keys : List String) : Option String :=
  match keys with
  | [] => none
  | key :: rest =>
      match fieldValue? fields key with
      | some value => some value
      | none => fieldValueAny? fields rest

def expectAtom (a : Assertion) (keys : List String) : Except String String := do
  match fieldValueAny? a.fields keys with
  | some value => pure (fieldAtom value)
  | none => throw s!"case {a.name}: missing expectation field among {keys}"

def expectBool (a : Assertion) (keys : List String) : Except String Bool := do
  match (← expectAtom a keys) with
  | "yes" => pure true
  | "no" => pure false
  | atom => throw s!"case {a.name}: expected yes/no field, got {atom}"

end BEDC.Rule110CrossCheck
