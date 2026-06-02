import BEDC.FKernel.Hist

namespace BEDC.Derived.CompactCauchyEquicontinuityUp

open BEDC.FKernel.Hist

inductive CompactCauchyEquicontinuityUp : Type where
  | mk
      (compactSource finiteNet pointwiseModulus cauchyFamily toleranceLedger regSeqRoute realSeal
        transport replay provenance localName : BHist) :
      CompactCauchyEquicontinuityUp
  deriving DecidableEq

theorem CompactCauchyEquicontinuityUp_nonempty :
    Nonempty CompactCauchyEquicontinuityUp := by
  exact
    ⟨CompactCauchyEquicontinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩

end BEDC.Derived.CompactCauchyEquicontinuityUp
