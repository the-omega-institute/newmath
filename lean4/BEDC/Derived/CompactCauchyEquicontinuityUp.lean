import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.CompactCauchyEquicontinuityUp

open BEDC.FKernel.Cont
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

theorem CompactCauchyEquicontinuityFiniteRoute
    (E : CompactCauchyEquicontinuityUp) :
    ∃ K F M W D R S H C P N compactFamily modulusRoute toleranceRoute realRoute : BHist,
      E = CompactCauchyEquicontinuityUp.mk K F M W D R S H C P N ∧
        Cont K F compactFamily ∧
          Cont compactFamily M modulusRoute ∧
            Cont modulusRoute D toleranceRoute ∧
              Cont toleranceRoute S realRoute ∧ hsame realRoute (append toleranceRoute S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases E with
  | mk K F M W D R S H C P N =>
      exact
        ⟨K, F, M, W, D, R, S, H, C, P, N, append K F, append (append K F) M,
          append (append (append K F) M) D, append (append (append (append K F) M) D) S,
          rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.CompactCauchyEquicontinuityUp
