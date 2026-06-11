import BEDC.Derived.DyadicIntervalCoverUp.BridgeFiniteRoute

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverBridgeRefinementBoundary [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N Lp Up Mp Rp Vp Wp Qp Ap Hp Cp Pp Np endpoint endpointp
      window windowp readback readbackp cover coverp sealRead sealReadp replay replayp :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg →
      DyadicIntervalCoverRootObligationSurface Lp Up Mp Rp Vp Wp Qp Ap Hp Cp Pp Np
          bundle pkg →
        hsame L Lp →
          hsame U Up →
            hsame M Mp →
              hsame R Rp →
                hsame V Vp →
                  hsame W Wp →
                    hsame Q Qp →
                      hsame A Ap →
                        hsame C Cp →
                          Cont L U endpoint →
                            Cont Lp Up endpointp →
                              Cont W Q window →
                                Cont Wp Qp windowp →
                                  Cont window R readback →
                                    Cont windowp Rp readbackp →
                                      Cont readback V cover →
                                        Cont readbackp Vp coverp →
                                          Cont cover A sealRead →
                                            Cont coverp Ap sealReadp →
                                              Cont sealRead C replay →
                                                Cont sealReadp Cp replayp →
                                                  PkgSig bundle replay pkg →
                                                    PkgSig bundle replayp pkg →
                                                      UnaryHistory endpoint ∧
                                                        UnaryHistory endpointp ∧
                                                          UnaryHistory window ∧
                                                            UnaryHistory windowp ∧
                                                              UnaryHistory readback ∧
                                                                UnaryHistory readbackp ∧
                                                                  UnaryHistory cover ∧
                                                                    UnaryHistory coverp ∧
                                                                      UnaryHistory sealRead ∧
                                                                        UnaryHistory sealReadp ∧
                                                                          UnaryHistory replay ∧
                                                                            UnaryHistory
                                                                              replayp ∧
                                                                              hsame endpoint
                                                                                endpointp ∧
                                                                                hsame window
                                                                                  windowp ∧
                                                                                  hsame readback
                                                                                    readbackp ∧
                                                                                    hsame cover
                                                                                      coverp ∧
                                                                                      hsame sealRead
                                                                                        sealReadp ∧
                                                                                        hsame replay
                                                                                          replayp := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro surface surfacep hL hU _hM hR hV hW hQ hA hC endpointRoute endpointRoutep
    windowRoute windowRoutep readbackRoute readbackRoutep coverRoute coverRoutep
    sealRoute sealRoutep replayRoute replayRoutep _replayPkg _replayPkgp
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A :=
    surface.right.right.right.right.right.right.right.left
  have cUnary : UnaryHistory C :=
    surface.right.right.right.right.right.right.right.right.right.left
  have lpUnary : UnaryHistory Lp := surfacep.left
  have upUnary : UnaryHistory Up := surfacep.right.left
  have rpUnary : UnaryHistory Rp := surfacep.right.right.right.left
  have vpUnary : UnaryHistory Vp := surfacep.right.right.right.right.left
  have wpUnary : UnaryHistory Wp := surfacep.right.right.right.right.right.left
  have qpUnary : UnaryHistory Qp := surfacep.right.right.right.right.right.right.left
  have apUnary : UnaryHistory Ap :=
    surfacep.right.right.right.right.right.right.right.left
  have cpUnary : UnaryHistory Cp :=
    surfacep.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lUnary uUnary endpointRoute
  have endpointpUnary : UnaryHistory endpointp :=
    unary_cont_closed lpUnary upUnary endpointRoutep
  have windowUnary : UnaryHistory window :=
    unary_cont_closed wUnary qUnary windowRoute
  have windowpUnary : UnaryHistory windowp :=
    unary_cont_closed wpUnary qpUnary windowRoutep
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have readbackpUnary : UnaryHistory readbackp :=
    unary_cont_closed windowpUnary rpUnary readbackRoutep
  have coverUnary : UnaryHistory cover :=
    unary_cont_closed readbackUnary vUnary coverRoute
  have coverpUnary : UnaryHistory coverp :=
    unary_cont_closed readbackpUnary vpUnary coverRoutep
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have sealpUnary : UnaryHistory sealReadp :=
    unary_cont_closed coverpUnary apUnary sealRoutep
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed sealUnary cUnary replayRoute
  have replaypUnary : UnaryHistory replayp :=
    unary_cont_closed sealpUnary cpUnary replayRoutep
  have hEndpoint : hsame endpoint endpointp :=
    cont_respects_hsame hL hU endpointRoute endpointRoutep
  have hWindow : hsame window windowp :=
    cont_respects_hsame hW hQ windowRoute windowRoutep
  have hReadback : hsame readback readbackp :=
    cont_respects_hsame hWindow hR readbackRoute readbackRoutep
  have hCover : hsame cover coverp :=
    cont_respects_hsame hReadback hV coverRoute coverRoutep
  have hSeal : hsame sealRead sealReadp :=
    cont_respects_hsame hCover hA sealRoute sealRoutep
  have hReplay : hsame replay replayp :=
    cont_respects_hsame hSeal hC replayRoute replayRoutep
  exact
    ⟨endpointUnary, endpointpUnary, windowUnary, windowpUnary, readbackUnary,
      readbackpUnary, coverUnary, coverpUnary, sealUnary, sealpUnary, replayUnary,
      replaypUnary, hEndpoint, hWindow, hReadback, hCover, hSeal, hReplay⟩

end BEDC.Derived.DyadicIntervalCoverUp
