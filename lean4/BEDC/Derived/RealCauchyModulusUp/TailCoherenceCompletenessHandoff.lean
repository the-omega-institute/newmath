import BEDC.Derived.RealCauchyModulusUp.TasteGate

namespace BEDC.Derived.RealCauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCauchyModulusCarrier_tail_coherence_completeness_handoff [AskSetup] [PackageSetup]
    {M S D Q E H C P N refinedWindow tailRead completionWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCauchyModulusCarrier M S D Q E H C P N bundle pkg →
      Cont S D refinedWindow →
        Cont refinedWindow Q tailRead →
          Cont tailRead E completionWitness →
            PkgSig bundle completionWitness pkg →
              UnaryHistory refinedWindow ∧ UnaryHistory tailRead ∧
                UnaryHistory completionWitness ∧ Cont S D refinedWindow ∧
                  Cont refinedWindow Q tailRead ∧ Cont tailRead E completionWitness ∧
                    PkgSig bundle completionWitness pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier refinedRoute tailRoute completionRoute completionPkg
  obtain ⟨_mUnary, sUnary, dUnary, qUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _modulusWindowRoute, _dyadicReadbackRoute, _sealRoute, _provenancePkg,
      _localSemantic⟩ := carrier
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed sUnary dUnary refinedRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed refinedUnary qUnary tailRoute
  have completionUnary : UnaryHistory completionWitness :=
    unary_cont_closed tailUnary eUnary completionRoute
  exact
    ⟨refinedUnary, tailUnary, completionUnary, refinedRoute, tailRoute, completionRoute,
      completionPkg⟩

end BEDC.Derived.RealCauchyModulusUp
