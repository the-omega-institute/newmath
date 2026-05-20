import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_zero_source_identity_boundary [AskSetup] [PackageSetup]
    {a b wa wb da db d e r h c p n zeroSeed zeroWindow zeroRead zeroSeal consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier a b wa wb da db d e r h c p n bundle pkg →
      Cont zeroSeed zeroWindow zeroRead →
        Cont zeroRead zeroSeal consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory zeroSeed →
              UnaryHistory zeroWindow →
                UnaryHistory zeroSeal →
                  UnaryHistory zeroRead ∧ UnaryHistory consumer ∧
                    Cont zeroSeed zeroWindow zeroRead ∧ Cont zeroRead zeroSeal consumer ∧
                      PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier zeroRoute sealRoute consumerPkg zeroSeedUnary zeroWindowUnary zeroSealUnary
  obtain ⟨_aUnary, _bUnary, _waUnary, _wbUnary, _daUnary, _dbUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _waRoute, _wbRoute, _sumRoute, _readbackRoute,
    _provenanceRoute, pPkg⟩ := carrier
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroSeedUnary zeroWindowUnary zeroRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed zeroReadUnary zeroSealUnary sealRoute
  exact ⟨zeroReadUnary, consumerUnary, zeroRoute, sealRoute, pPkg, consumerPkg⟩

end BEDC.Derived.RegularCauchySumUp
