import BEDC.Derived.DiagonalCofinalTailUp
import BEDC.Derived.RegularCauchyZeroUp.RealSealNonescape

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalCofinalTailCarrier_zero_source_terminal_coincidence [AskSetup] [PackageSetup]
    {q s g d r w h c p n zq zs zr zm zmu ze zh zc zp zn terminalRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      BEDC.Derived.RegularCauchyZeroUp.RegularCauchyZeroCarrier zq zs zr zm zmu ze zh zc zp zn ->
        hsame q zq ->
          hsame s zs ->
            hsame g zr ->
              hsame d zm ->
                hsame r ze ->
                  Cont r w terminalRead ->
                    Cont terminalRead c completionRead ->
                      PkgSig bundle completionRead pkg ->
                        UnaryHistory terminalRead ∧ UnaryHistory completionRead ∧ hsame q zq ∧
                          hsame s zs ∧ hsame g zr ∧ hsame d zm ∧ hsame r ze ∧
                            Cont r w terminalRead ∧ Cont terminalRead c completionRead ∧
                              PkgSig bundle p pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier zeroCarrier sameQ sameS sameG sameD sameR terminalRoute completionRoute
    completionPkg
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, rUnary, wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  obtain ⟨_zqUnary, _zsUnary, _zrUnary, _zmUnary, _zmuUnary, _zeUnary, _zcUnary,
    _zpUnary, _znUnary, _zqsRoute, _zrmRoute, _zmuSealRoute, _zeroAppend⟩ :=
    zeroCarrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed rUnary wUnary terminalRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed terminalUnary cUnary completionRoute
  exact
    ⟨terminalUnary, completionUnary, sameQ, sameS, sameG, sameD, sameR, terminalRoute,
      completionRoute, pPkg, completionPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
