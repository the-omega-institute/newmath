import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationRegSeqRatRealSealRoute [AskSetup] [PackageSetup]
    {W M Q T S H C P N toleranceRead tailRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier W M Q T S H C P N bundle pkg →
      Cont W Q toleranceRead →
        Cont toleranceRead T tailRead →
          Cont tailRead S sealRead →
            Cont sealRead N namedRead →
              PkgSig bundle namedRead pkg →
                UnaryHistory toleranceRead ∧ UnaryHistory tailRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory namedRead ∧
                    Cont W Q toleranceRead ∧ Cont toleranceRead T tailRead ∧
                      Cont tailRead S sealRead ∧ Cont sealRead N namedRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier toleranceRoute tailRoute sealRoute namedRoute namedPkg
  obtain ⟨wUnary, _mUnary, qUnary, tUnary, sUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _wMRoute, _mQRoute, _tSRoute, _cNRoute, provenancePkg⟩ := carrier
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed wUnary qUnary toleranceRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  exact
    ⟨toleranceUnary, tailUnary, sealUnary, namedUnary, toleranceRoute, tailRoute,
      sealRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.CauchyOscillationUp
