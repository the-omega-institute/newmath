import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem MatrixSingletonCarrier_semanticNameCert :
    SemanticNameCert MatrixSingletonCarrier MatrixSingletonCarrier MatrixSingletonCarrier hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
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
        intro _h _k same carrier
        exact hsame_trans (hsame_symm same) carrier
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

end BEDC.Derived.MatrixUp
