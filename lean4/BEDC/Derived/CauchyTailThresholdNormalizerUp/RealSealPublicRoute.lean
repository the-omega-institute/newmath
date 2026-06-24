import BEDC.Derived.CauchyTailThresholdNormalizerUp.PublicCertificate

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailThresholdNormalizerRealSealPublicRoute [AskSetup] [PackageSetup]
    {S M Theta W0 W1 D R A E H C P L N terminalRead routeRead publicRead
      realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailThresholdNormalizerCarrier S M Theta W0 W1 D R A E H C P L N
        bundle pkg →
      Cont S M Theta →
        Cont Theta W0 W1 →
          Cont W1 D R →
            Cont R A E →
              Cont E C terminalRead →
                Cont terminalRead N routeRead →
                  Cont routeRead L publicRead →
                    Cont publicRead E realSealRead →
                      PkgSig bundle realSealRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row M ∨ hsame row Theta ∨
                                hsame row W0 ∨ hsame row W1 ∨ hsame row D ∨
                                  hsame row R ∨ hsame row A ∨ hsame row E ∨
                                    hsame row H ∨ hsame row C ∨ hsame row P ∨
                                      hsame row L ∨ hsame row N ∨
                                        hsame row publicRead ∨ hsame row realSealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont publicRead E realSealRead ∧
                                PkgSig bundle realSealRead pkg)
                            hsame ∧
                          UnaryHistory realSealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sourceRoute thresholdRoute readbackRoute agreementRoute terminalRoute
    routeRoute publicRoute realSealRoute realSealPkg
  obtain ⟨sUnary, mUnary, _thetaUnary, w0Unary, _w1Unary, dUnary, _rUnary, aUnary,
    eUnary, _hUnary, cUnary, _pUnary, lUnary, nUnary, _thresholdWindow, _pkgP,
    _pkgN⟩ := carrier
  have thetaRouteUnary : UnaryHistory Theta :=
    unary_cont_closed sUnary mUnary sourceRoute
  have w1RouteUnary : UnaryHistory W1 :=
    unary_cont_closed thetaRouteUnary w0Unary thresholdRoute
  have rRouteUnary : UnaryHistory R :=
    unary_cont_closed w1RouteUnary dUnary readbackRoute
  have eRouteUnary : UnaryHistory E :=
    unary_cont_closed rRouteUnary aUnary agreementRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed eRouteUnary cUnary terminalRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed terminalUnary nUnary routeRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary lUnary publicRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed publicUnary eUnary realSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨
              hsame row W1 ∨ hsame row D ∨ hsame row R ∨ hsame row A ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row L ∨ hsame row N ∨ hsame row publicRead ∨
                    hsame row realSealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont publicRead E realSealRead ∧
              PkgSig bundle realSealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSealRead
        ⟨hsame_refl realSealRead, realSealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealRoute, realSealPkg⟩
  }
  exact ⟨cert, realSealUnary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
