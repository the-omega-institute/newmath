import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_window_selector_uniqueness [AskSetup]
    [PackageSetup]
    {m0 m1 u v t w q e h c p n m0' m1' u' v' t' w' q' e' h' c' p' n' sealRead
      sealRead' terminalRead terminalRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      CauchyModulusRefinementCarrier m0' m1' u' v' t' w' q' e' h' c' p' n'
          bundle pkg →
        hsame t t' →
          hsame w w' →
            hsame q q' →
              hsame e e' →
                Cont t w q →
                  Cont t' w' q' →
                    Cont q e sealRead →
                      Cont q' e' sealRead' →
                        Cont w sealRead terminalRead →
                          Cont w' sealRead' terminalRead' →
                            hsame sealRead sealRead' ∧ hsame terminalRead terminalRead' ∧
                              UnaryHistory sealRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier carrier' sameT sameW sameQ sameE twqRoute twqRoute' qSeal qSeal'
    terminalRoute terminalRoute'
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, wUnary, qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩
  rcases carrier' with
    ⟨_m0Unary', _m1Unary', _uUnary', _vUnary', _tUnary', wUnary', qUnary',
      eUnary', _hUnary', _cUnary', _pUnary', _nUnary', _m0m1u', _uvt', _twq',
      _qeh', _pPkg', _hn'⟩
  have _sameQFromRoute : hsame q q' :=
    cont_respects_hsame sameT sameW twqRoute twqRoute'
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary qSeal
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed qUnary' eUnary' qSeal'
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed wUnary sealReadUnary terminalRoute
  have _terminalReadUnary' : UnaryHistory terminalRead' :=
    unary_cont_closed wUnary' sealReadUnary' terminalRoute'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameQ sameE qSeal qSeal'
  have sameTerminalRead : hsame terminalRead terminalRead' :=
    cont_respects_hsame sameW sameSealRead terminalRoute terminalRoute'
  exact ⟨sameSealRead, sameTerminalRead, sealReadUnary, terminalReadUnary⟩

end BEDC.Derived.CauchyModulusRefinementUp
