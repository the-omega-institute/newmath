import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive TubeLemmaFiniteProductUp : Type where
  | mk
      (index factorTopology compactSlice productOpen coordinateNeighbourhood tubeNeighbourhood
        finiteCover coordinateRoute transport replay provenance name :
          _root_.BEDC.FKernel.Hist.BHist) :
      TubeLemmaFiniteProductUp

end BEDC.Derived
