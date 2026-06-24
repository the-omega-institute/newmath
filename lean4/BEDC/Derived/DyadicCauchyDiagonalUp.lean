import BEDC.FKernel.Hist

namespace BEDC.Derived.DyadicCauchyDiagonalUp

open BEDC.FKernel.Hist

structure DyadicCauchyDiagonalUp where
  dyadicTolerance : BHist
  streamWindow : BHist
  regularReadback : BHist
  diagonalRow : BHist
  realSeal : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist

end BEDC.Derived.DyadicCauchyDiagonalUp
