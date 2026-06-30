import BedcMathlibBridge.Constructive.Bool

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

end BedcMathlibBridge.Export.Bool
