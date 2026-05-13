import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Ext
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.FKernel.Ask
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.Package
import BEDC.FKernel.Gap
import BEDC.FKernel.NameCert
import BEDC.FKernel.Settled
import BEDC.GroundCompiler.ChannelEncoding
import Rule110CrossCheck.Decoder
import Rule110CrossCheck.Reporting

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

def checkBundleLengthTheorem (theoremName : String) (bundles : List (List Nat)) : Bool :=
  match theoremName, bundles with
  | "bundleLength_append", [a, b] => (bundleAppendList a b).length == a.length + b.length
  | "bundleAppend_nil_right", [a] => bundleAppendList a [] == a
  | "bundleAppend_assoc", [a, b, c] => bundleAppendList a (bundleAppendList b c) == bundleAppendList (bundleAppendList a b) c
  | "bundleAppend_eq_right_iff_left_nil", [a, b] => (bundleAppendList a b == b) == (a == [])
  | "bundleAppend_eq_left_iff_right_nil", [a, b] => (bundleAppendList a b == a) == (b == [])
  | "bundleAppend_split_unique_fixed_length", [a, b, c, d] =>
      !((bundleAppendList a b == bundleAppendList c d) && a.length == c.length) || (a == c && b == d)
  | "bundleAppend_split_unique_fixed_suffix_length", [a, b, c, d] =>
      !((bundleAppendList a b == bundleAppendList c d) && b.length == d.length) || (a == c && b == d)
  | "bundleAppend_three_split_unique_fixed_lengths", [a, b, c, d, e, f] =>
      !((bundleAppendList a (bundleAppendList b c) == bundleAppendList d (bundleAppendList e f)) &&
          a.length == d.length && b.length == e.length) || (a == d && b == e && c == f)
  | _, _ => false

def bundleLengthArity (theoremName : String) : Except String Nat :=
  match theoremName with
  | "bundleLength_append" => pure 2
  | "bundleAppend_nil_right" => pure 1
  | "bundleAppend_assoc" => pure 3
  | "bundleAppend_eq_right_iff_left_nil" => pure 2
  | "bundleAppend_eq_left_iff_right_nil" => pure 2
  | "bundleAppend_split_unique_fixed_length" => pure 4
  | "bundleAppend_split_unique_fixed_suffix_length" => pure 4
  | "bundleAppend_three_split_unique_fixed_lengths" => pure 6
  | other => throw s!"unsupported bundle length theorem {other}"

def checkBundleLength (path : String) (a : Assertion) : Except String String := do
  let theoremName <- match fieldValue? a.fields "theorem" with
    | some t => pure (fieldAtom t)
    | none => throw s!"case {a.name}: missing theorem field"
  let expected <- expectBool a ["conclusion_holds"]
  let events <- decodeAllEvents a.input
  let arity <- bundleLengthArity theoremName
  let (bundles, rest) <- parseNBundlesFor .bundleLength arity events
  requireNoRest rest
  boolExpected (checkBundleLengthTheorem theoremName bundles) expected
  pure (passLine path .bundleLength a s!"{bundles.map natListLabel}" s!"theorem={theoremName}")

def checkBundleMembershipTheorem (theoremName : String) (probe? : Option Nat) (bundles : List (List Nat)) : Bool :=
  match theoremName, probe?, bundles with
  | "inBundle_nil_elim", some p, [a] => !(bundleContains p a)
  | "inBundle_cons_self", some p, [a] => match a with | x :: _ => x == p && bundleContains p a | [] => false
  | "inBundle_singleton_iff", some p, [a] => a.length == 1 && (bundleContains p a == (some p == a.head?))
  | "inBundle_bundleAppend_iff", some p, [a, b] => bundleContains p (bundleAppendList a b) == (bundleContains p a || bundleContains p b)
  | "inBundle_bundleAppend_left_of_not_right", some p, [a, b] =>
      !(bundleContains p (bundleAppendList a b) && !bundleContains p b) || bundleContains p a
  | "inBundle_bundleAppend_right_of_not_left", some p, [a, b] =>
      !(bundleContains p (bundleAppendList a b) && !bundleContains p a) || bundleContains p b
  | "inBundle_bundleAppend_three_iff", some p, [a, b, c] =>
      bundleContains p (bundleAppendList a (bundleAppendList b c)) == (bundleContains p a || bundleContains p b || bundleContains p c)
  | "inBundle_bundleAppend_four_iff", some p, [a, b, c, d] =>
      bundleContains p (bundleAppendList a (bundleAppendList b (bundleAppendList c d))) ==
        (bundleContains p a || bundleContains p b || bundleContains p c || bundleContains p d)
  | "inBundle_member_split_iff", some p, [a] => bundleContains p a == bundleContains p a
  | "bundleAppend_cancellation", none, [a, b, c, d] =>
      (!(bundleAppendList a b == bundleAppendList a c) || b == c) &&
        (!(bundleAppendList b d == bundleAppendList c d) || b == c)
  | "bundleAppend_cons_result_iff", none, [a, b, c] =>
      c.length > 0 &&
        (!(bundleAppendList a b == c) ||
          match a with
          | [] => b == c
          | _ :: tail => bundleAppendList tail b == c.drop 1)
  | "bundleAppend_empty_result_inversion", none, [a, b] =>
      !((bundleAppendList a b).length == 0) || (a == [] && b == [])
  | _, _, _ => false

def bundleMembershipShape (theoremName : String) : Except String (Bool × Nat) :=
  match theoremName with
  | "inBundle_nil_elim" => pure (true, 1)
  | "inBundle_cons_self" => pure (true, 1)
  | "inBundle_singleton_iff" => pure (true, 1)
  | "inBundle_bundleAppend_iff" => pure (true, 2)
  | "inBundle_bundleAppend_left_of_not_right" => pure (true, 2)
  | "inBundle_bundleAppend_right_of_not_left" => pure (true, 2)
  | "inBundle_bundleAppend_three_iff" => pure (true, 3)
  | "inBundle_bundleAppend_four_iff" => pure (true, 4)
  | "inBundle_member_split_iff" => pure (true, 1)
  | "bundleAppend_cancellation" => pure (false, 4)
  | "bundleAppend_cons_result_iff" => pure (false, 3)
  | "bundleAppend_empty_result_inversion" => pure (false, 2)
  | other => throw s!"unsupported bundle membership theorem {other}"

def checkBundleMembership (path : String) (a : Assertion) : Except String String := do
  let theoremName <- match fieldValue? a.fields "theorem" with
    | some t => pure (fieldAtom t)
    | none => throw s!"case {a.name}: missing theorem field"
  let expected <- expectBool a ["conclusion_holds"]
  let events <- decodeAllEvents a.input
  let (hasProbe, arity) <- bundleMembershipShape theoremName
  let (probe?, rest) <- if hasProbe then
      let (p, rest) <- parseNatFromEvents events
      pure (some p, rest)
    else
      pure (none, events)
  let (bundles, rest) <- parseNBundlesFor .bundleMembership arity rest
  requireNoRest rest
  boolExpected (checkBundleMembershipTheorem theoremName probe? bundles) expected
  pure (passLine path .bundleMembership a s!"probe={probe?} bundles={bundles.map natListLabel}" s!"theorem={theoremName}")

end BEDC.Rule110CrossCheck
