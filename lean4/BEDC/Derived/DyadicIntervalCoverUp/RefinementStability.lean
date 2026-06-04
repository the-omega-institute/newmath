import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRefinementStability [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N L' U' M' R' V' W' Q' A' H' C' P' N' endpoint
      endpoint' window window' cover cover' sealRead sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      DyadicIntervalCoverRootObligationSurface L' U' M' R' V' W' Q' A' H' C' P' N'
          bundle pkg →
        hsame L L' →
          hsame U U' →
            hsame M M' →
              hsame R R' →
                hsame V V' →
                  hsame W W' →
                    hsame Q Q' →
                      hsame A A' →
                        Cont L U endpoint →
                          Cont L' U' endpoint' →
                            Cont W Q window →
                              Cont W' Q' window' →
                                Cont M R cover →
                                  Cont M' R' cover' →
                                    Cont cover A sealRead →
                                      Cont cover' A' sealRead' →
                                        PkgSig bundle sealRead pkg →
                                          PkgSig bundle sealRead' pkg →
                                            UnaryHistory endpoint ∧
                                              UnaryHistory endpoint' ∧
                                                UnaryHistory window ∧
                                                  UnaryHistory window' ∧
                                                    UnaryHistory cover ∧
                                                      UnaryHistory cover' ∧
                                                        UnaryHistory sealRead ∧
                                                          UnaryHistory sealRead' ∧
                                                            hsame endpoint endpoint' ∧
                                                              hsame window window' ∧
                                                                hsame cover cover' ∧
                                                                  hsame sealRead sealRead' := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro surface surface' sameL sameU sameM sameR _sameV sameW sameQ sameA endpointCont
    endpointCont' windowCont windowCont' coverCont coverCont' sealCont sealCont' _sealPkg
    _sealPkg'
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have mUnary : UnaryHistory M := surface.right.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have lUnary' : UnaryHistory L' := surface'.left
  have uUnary' : UnaryHistory U' := surface'.right.left
  have mUnary' : UnaryHistory M' := surface'.right.right.left
  have rUnary' : UnaryHistory R' := surface'.right.right.right.left
  have wUnary' : UnaryHistory W' := surface'.right.right.right.right.right.left
  have qUnary' : UnaryHistory Q' := surface'.right.right.right.right.right.right.left
  have aUnary' : UnaryHistory A' := surface'.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint := unary_cont_closed lUnary uUnary endpointCont
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed lUnary' uUnary' endpointCont'
  have windowUnary : UnaryHistory window := unary_cont_closed wUnary qUnary windowCont
  have windowUnary' : UnaryHistory window' := unary_cont_closed wUnary' qUnary' windowCont'
  have coverUnary : UnaryHistory cover := unary_cont_closed mUnary rUnary coverCont
  have coverUnary' : UnaryHistory cover' := unary_cont_closed mUnary' rUnary' coverCont'
  have sealUnary : UnaryHistory sealRead := unary_cont_closed coverUnary aUnary sealCont
  have sealUnary' : UnaryHistory sealRead' := unary_cont_closed coverUnary' aUnary' sealCont'
  cases sameL
  cases sameU
  have sameEndpoint : hsame endpoint endpoint' := endpointCont.trans endpointCont'.symm
  cases sameW
  cases sameQ
  have sameWindow : hsame window window' := windowCont.trans windowCont'.symm
  cases sameM
  cases sameR
  have sameCover : hsame cover cover' := coverCont.trans coverCont'.symm
  have sameCoverFinal : hsame cover cover' := sameCover
  cases sameA
  cases sameCover
  have sameSeal : hsame sealRead sealRead' := sealCont.trans sealCont'.symm
  exact
    ⟨endpointUnary, endpointUnary', windowUnary, windowUnary', coverUnary, coverUnary',
      sealUnary, sealUnary', sameEndpoint, sameWindow, sameCoverFinal, sameSeal⟩

end BEDC.Derived.DyadicIntervalCoverUp
