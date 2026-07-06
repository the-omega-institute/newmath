import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CantorBarModulusUp : Type where
  | mk
      (cantorSpace decidableBar fanTheorem streamName regSeqRat realSeal transport replay
        exportRow provenance localNameCert : BHist) :
      CantorBarModulusUp
  deriving DecidableEq

end BEDC.Derived
