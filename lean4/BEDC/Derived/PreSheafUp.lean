import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PreSheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def PreSheafIndexedRestrictionSurface (openHist sectionHist restricted : BHist) : Prop :=
  UnaryHistory openHist ∧ UnaryHistory sectionHist ∧ Cont openHist sectionHist restricted

theorem PreSheafRestrictionFunctoriality_obligations
    {openA openB sectionHist overAB overBC viaAB direct ledger : BHist} :
    PreSheafIndexedRestrictionSurface openA openB overAB ->
      PreSheafIndexedRestrictionSurface overAB sectionHist viaAB ->
        PreSheafIndexedRestrictionSurface openB sectionHist overBC ->
          PreSheafIndexedRestrictionSurface openA overBC direct ->
            Cont viaAB direct ledger ->
              hsame viaAB direct ∧ UnaryHistory viaAB ∧ UnaryHistory direct ∧
                UnaryHistory ledger := by
  intro surfaceAB surfaceVia surfaceBC surfaceDirect ledgerRow
  have sameRoutes : hsame viaAB direct :=
    cont_assoc_hsame surfaceAB.right.right surfaceVia.right.right
      surfaceBC.right.right surfaceDirect.right.right
  have viaUnary : UnaryHistory viaAB :=
    unary_cont_closed surfaceVia.left surfaceVia.right.left surfaceVia.right.right
  have directUnary : UnaryHistory direct :=
    unary_cont_closed surfaceDirect.left surfaceDirect.right.left surfaceDirect.right.right
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed viaUnary directUnary ledgerRow
  exact And.intro sameRoutes
    (And.intro viaUnary (And.intro directUnary ledgerUnary))

end BEDC.Derived.PreSheafUp
