import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive BishopApartnessFieldEnvelopeUp : Type where
  | mk
      (regularSource realSeal apartnessPositive apartnessBudget fieldEnvelope
        mixedHandoff transport replay provenance name : _root_.BEDC.FKernel.Hist.BHist) :
      BishopApartnessFieldEnvelopeUp

end BEDC.Derived
