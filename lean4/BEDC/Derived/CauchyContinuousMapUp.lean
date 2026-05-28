import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

structure CauchyContinuousMapUp where
  windows : BHist
  imageReadback : BHist
  toleranceLedger : BHist
  realSealHandoff : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist
deriving DecidableEq

namespace CauchyContinuousMapUp

theorem CauchyContinuousMap_regseqrat_image (M : BEDC.Derived.CauchyContinuousMapUp)
    {windowTolerance imageRead : BHist} :
    Cont M.windows M.toleranceLedger windowTolerance ->
      Cont windowTolerance M.imageReadback imageRead ->
        hsame imageRead (append M.windows (append M.toleranceLedger M.imageReadback)) ∧
          hsame M.imageReadback M.imageReadback := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  intro windowRoute imageRoute
  constructor
  · exact imageRoute.trans (congrArg (fun row => append row M.imageReadback) windowRoute)
      |>.trans (append_assoc M.windows M.toleranceLedger M.imageReadback)
  · exact hsame_refl M.imageReadback

end CauchyContinuousMapUp

end BEDC.Derived
