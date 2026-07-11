import BedcMathlibBridge.Constructive.Bool
import BEDC.HostBridge.ChurchBoolPairRoundTrip
import Mathlib.Data.Bool.Basic

namespace BedcMathlibBridge.Export.Bool

open BedcMathlibBridge.Constructive.Bool.BoolUp

structure BoolExportWitness where
  carrierEquiv : CBool ≃ _root_.Bool
  toBool_apply : ∀ b : CBool, carrierEquiv.toFun b = toBool b
  ofBool_apply : ∀ b : _root_.Bool, carrierEquiv.invFun b = ofBool b
  false_apply : toBool BEDC.FKernel.Mark.BMark.b0 = false
  true_apply : toBool BEDC.FKernel.Mark.BMark.b1 = true
  classifier_apply : ∀ b c : CBool,
    BEDC.Derived.BoolUp.BoolClassifierSpec b c ↔ toBool b = toBool c
  endpoint_readback_apply : ∀ b c : CBool,
    BEDC.Derived.BoolUp.BoolClassifierSpec b c ↔
      BEDC.FKernel.Hist.hsame
        (BEDC.Derived.BoolUp.BoolEndpoint b)
        (BEDC.Derived.BoolUp.BoolEndpoint c)

def boolExport : BoolExportWitness where
  carrierEquiv := boolUpEquiv
  toBool_apply := by
    intro b
    rfl
  ofBool_apply := by
    intro b
    rfl
  false_apply := toBool_b0
  true_apply := toBool_b1
  classifier_apply := classifier_iff_toBool_eq
  endpoint_readback_apply := classifier_iff_endpoint_hsame_via_stdBridge

structure BoolMathlibCorrespondence (A B : Type) where
  carrierEquiv : A ≃ B
  classifier_apply : ∀ b c : CBool,
    BEDC.Derived.BoolUp.BoolClassifierSpec b c ↔ toBool b = toBool c
  endpoint_readback_apply : ∀ b c : CBool,
    BEDC.Derived.BoolUp.BoolClassifierSpec b c ↔
      BEDC.FKernel.Hist.hsame
        (BEDC.Derived.BoolUp.BoolEndpoint b)
        (BEDC.Derived.BoolUp.BoolEndpoint c)

def bool_mathlib_correspondence : BoolMathlibCorrespondence CBool _root_.Bool where
  carrierEquiv := boolExport.carrierEquiv
  classifier_apply := boolExport.classifier_apply
  endpoint_readback_apply := classifier_iff_endpoint_hsame_via_stdBridge

structure BoolAndOrderExportWitness where
  church_and : Bool → Bool → BEDC.MetaCIC.Term
  church_and_apply : ∀ a b : Bool,
    church_and a b = BEDC.HostBridge.hostBoolAndChurch a b
  church_and_beta : ∀ a b : Bool,
    BEDC.MetaCIC.BetaStarStep
      (church_and a b)
      (BEDC.HostBridge.hostBoolToChurch (a && b))
  mathlib_and_le_left : ∀ a b : Bool, (a && b) ≤ a
  mathlib_and_le_left_apply : ∀ a b : Bool,
    mathlib_and_le_left a b = Bool.and_le_left a b

def boolAndOrderExport : BoolAndOrderExportWitness where
  church_and := BEDC.HostBridge.hostBoolAndChurch
  church_and_apply := by
    intro a b
    rfl
  church_and_beta := BEDC.HostBridge.hostBoolAndChurch_beta
  mathlib_and_le_left := Bool.and_le_left
  mathlib_and_le_left_apply := by
    intro a b
    rfl

theorem bool_and_le_left_mathlib_correspondence :
    (∀ a b : Bool,
      boolAndOrderExport.church_and_beta a b =
        BEDC.HostBridge.hostBoolAndChurch_beta a b) ∧
    (∀ a b : Bool,
      boolAndOrderExport.mathlib_and_le_left a b =
        Bool.and_le_left a b) := by
  constructor
  · intro a b
    change
      BEDC.HostBridge.hostBoolAndChurch_beta a b =
        BEDC.HostBridge.hostBoolAndChurch_beta a b
    exact Eq.refl (BEDC.HostBridge.hostBoolAndChurch_beta a b)
  · intro a b
    change Bool.and_le_left a b = Bool.and_le_left a b
    exact Eq.refl (Bool.and_le_left a b)

end BedcMathlibBridge.Export.Bool
