import Rule110CrossCheck.Decoder.Bundles

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

def bundleAppendList (a b : List Nat) : List Nat := a ++ b

def bundleContains (p : Nat) : List Nat -> Bool
  | [] => false
  | x :: xs => x == p || bundleContains p xs

def sigResult (bundle : List Nat) (h : BHist) : BHist :=
  bundle.foldr (fun p acc => extResult acc (askExpected p h)) BHist.Empty

def sameSigFixture (bundle : List Nat) (h k : BHist) : Bool :=
  sigResult bundle h == sigResult bundle k

def unaryHistoryBool : BHist -> Bool
  | BHist.Empty => true
  | BHist.e1 h => unaryHistoryBool h
  | BHist.e0 _ => false

def tokIntroBool (s p : BHist) : Bool := s == p

def psameBool (s t p q : BHist) : Bool :=
  tokIntroBool s p && tokIntroBool t q && s == t

end BEDC.Rule110CrossCheck
