import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive NewtonForwardSeriesUp : Type where
  | mk
      (baseAndStep forwardTable coefficientRow reconstruction regularReadback
        cauchyWindow transport replay provenance localNameCert : BHist) :
      NewtonForwardSeriesUp
  deriving DecidableEq

end BEDC.Derived
