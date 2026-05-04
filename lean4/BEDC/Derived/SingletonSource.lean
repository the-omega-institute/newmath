import BEDC.FKernel.NameCert

namespace BEDC.Derived.SingletonSource

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SingletonHistorySource (a0 : BHist) (x : BHist) : Prop :=
  hsame x a0

theorem SingletonHistorySource_name_certificate (a0 : BHist) :
    NameCert (SingletonHistorySource a0) hsame := by
  have semantic : SemanticNameCert (SingletonHistorySource a0) (SingletonHistorySource a0)
      (SingletonHistorySource a0) hsame := {
    core := {
      carrier_inhabited := Exists.intro a0 (hsame_refl a0)
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro _h _k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }
  exact semantic.core

end BEDC.Derived.SingletonSource
