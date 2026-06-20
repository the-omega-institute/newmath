import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LebesgueConstantUp : Type where
  | mk
      (fourierWindow dirichletRow phaseSamples integralNormalization normLedger
        dyadicTolerance regSeqRatReadback realSeal transport replay provenance localName : BHist) :
      LebesgueConstantUp

end BEDC.Derived
