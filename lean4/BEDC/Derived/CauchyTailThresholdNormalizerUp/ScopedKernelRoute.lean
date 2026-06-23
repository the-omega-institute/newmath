import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailThresholdNormalizerScopedKernelRoute [AskSetup] [PackageSetup]
    {S M Theta W0 W1 D R A E H C P L N terminalRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailThresholdNormalizerCarrier S M Theta W0 W1 D R A E H C P L N
        bundle pkg ->
      Cont S M Theta ->
        Cont Theta W0 W1 ->
          Cont W1 D R ->
            Cont R A E ->
              Cont E C terminalRead ->
                Cont terminalRead N routeRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle routeRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row M ∨ hsame row Theta ∨
                              hsame row W0 ∨ hsame row W1 ∨ hsame row D ∨
                                hsame row R ∨ hsame row A ∨ hsame row E ∨
                                  hsame row H ∨ hsame row C ∨ hsame row P ∨
                                    hsame row L ∨ hsame row N ∨
                                      hsame row terminalRead ∨ hsame row routeRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont S M Theta ∧ Cont Theta W0 W1 ∧
                              Cont W1 D R ∧ Cont R A E ∧ Cont E C terminalRead ∧
                                Cont terminalRead N routeRead ∧ PkgSig bundle routeRead pkg)
                          hsame ∧
                        UnaryHistory terminalRead ∧ UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sourceRoute thresholdRoute readbackRoute agreementRoute terminalRoute routeRoute
    _provenancePkg routePkg
  obtain ⟨_sUnary, _mUnary, _thetaUnary, _w0Unary, _w1Unary, _dUnary, _rUnary,
    _aUnary, eUnary, _hUnary, cUnary, _pUnary, _lUnary, nUnary, _thresholdWindow,
    _pkgP, _pkgN⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed eUnary cUnary terminalRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed terminalUnary nUnary routeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨
              hsame row W1 ∨ hsame row D ∨ hsame row R ∨ hsame row A ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row L ∨ hsame row N ∨ hsame row terminalRead ∨
                    hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M Theta ∧ Cont Theta W0 W1 ∧ Cont W1 D R ∧
              Cont R A E ∧ Cont E C terminalRead ∧ Cont terminalRead N routeRead ∧
                PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead
        ⟨hsame_refl routeRead, routeUnary⟩
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
      exact
        ⟨source.right, sourceRoute, thresholdRoute, readbackRoute, agreementRoute,
          terminalRoute, routeRoute, routePkg⟩
  }
  exact ⟨cert, terminalUnary, routeUnary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
