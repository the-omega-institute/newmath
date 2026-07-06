import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive FoxArtinArcUp : Type where
  | carrier
      (arc ambientEnd compactWindow wildEnd tameShadow knotShadow topologyRoute :
        BEDC.FKernel.Hist.BHist)

end BEDC.Derived
