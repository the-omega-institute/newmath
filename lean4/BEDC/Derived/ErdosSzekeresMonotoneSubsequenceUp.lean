import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ErdosSzekeresMonotoneSubsequenceUp : Type where
  | mk
      (sourceWindows increasingRows decreasingRows listSpine orderLedger ramseyRows transportRows
        replayRows provenanceRows nameRows : BHist) : ErdosSzekeresMonotoneSubsequenceUp
  deriving DecidableEq

