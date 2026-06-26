import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive ExpLogBisectionUp : Type where
  | mk
      (positiveInput initialBracket bisectionLedger exponentialComparison logarithmEndpoint
        streamWindows dyadicLedger regularReadback realSeal transport replay provenance name :
          _root_.BEDC.FKernel.Hist.BHist) :
      ExpLogBisectionUp

end BEDC.Derived
