import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ToeplitzSilvermanUp : Type where
  | mk
      (matrixWindow rowBound columnVanishing sourceWindow transformedRow regularReadback realSeal
        transport replay package name : BHist) :
      ToeplitzSilvermanUp
  deriving DecidableEq

def toeplitzSilvermanFields : ToeplitzSilvermanUp → List BHist
  | ToeplitzSilvermanUp.mk matrixWindow rowBound columnVanishing sourceWindow transformedRow
      regularReadback realSeal transport replay package name =>
      [matrixWindow, rowBound, columnVanishing, sourceWindow, transformedRow, regularReadback,
        realSeal, transport, replay, package, name]

end BEDC.Derived
