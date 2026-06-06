import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MackeyDecompositionUp : Type where
  | mk
      (group subgroup representation induced restricted doubleCoset transporter schur
        frobenius ledger provenance nameRow : BHist) :
      MackeyDecompositionUp

end BEDC.Derived
