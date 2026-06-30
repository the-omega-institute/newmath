import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive TraceClassOperatorUp : Type where
  | mk (hilbert bounded ideal spectral real rational trace transport replay provenance localName :
      BHist) : TraceClassOperatorUp
  deriving DecidableEq

end BEDC.Derived
