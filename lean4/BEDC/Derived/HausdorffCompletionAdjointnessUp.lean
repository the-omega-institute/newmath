import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive HausdorffCompletionAdjointnessUp : Type where
  | mk
      (completionSource hausdorffReflection unitRow counitRow streamWindows regularReadback
        realSeal transport replay provenance localNameCert : BHist) :
      HausdorffCompletionAdjointnessUp
  deriving DecidableEq

end BEDC.Derived
