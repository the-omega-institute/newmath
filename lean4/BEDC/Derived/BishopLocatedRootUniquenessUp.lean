import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopLocatedRootUniquenessUp : Type where
  | mk
      (leftRootRead rightRootRead separationApartness sharedBisectionRoute leftRegSeqRat
        rightRegSeqRat leftRealSeal rightRealSeal transport replay provenance localNameCert :
          BHist) :
      BishopLocatedRootUniquenessUp
  deriving DecidableEq

end BEDC.Derived
