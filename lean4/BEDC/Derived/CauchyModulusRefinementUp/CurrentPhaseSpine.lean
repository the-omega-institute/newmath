import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_current_phase_spine
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n dyadic stream regseq real : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      UnaryHistory regseq →
        Cont w regseq stream →
          Cont q stream dyadic →
            Cont q e real →
              PkgSig bundle real pkg →
                UnaryHistory q ∧ UnaryHistory w ∧ UnaryHistory e ∧
                  UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory real ∧
                    Cont t w q ∧ Cont q stream dyadic ∧ Cont w regseq stream ∧
                      Cont q e real ∧ PkgSig bundle p pkg ∧ PkgSig bundle real pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier regseqUnary wRegseqStream qStreamDyadic qEReal realPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, twq, _qeh, pPkg, _hn⟩
  have streamUnary : UnaryHistory stream :=
    unary_cont_closed wUnary regseqUnary wRegseqStream
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed qUnary streamUnary qStreamDyadic
  have realUnary : UnaryHistory real :=
    unary_cont_closed qUnary eUnary qEReal
  exact
    ⟨qUnary, wUnary, eUnary, dyadicUnary, streamUnary, realUnary, twq, qStreamDyadic,
      wRegseqStream, qEReal, pPkg, realPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
