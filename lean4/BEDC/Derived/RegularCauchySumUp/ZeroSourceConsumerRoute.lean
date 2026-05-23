import BEDC.Derived.RegularCauchySumUp

namespace BEDC.Derived.RegularCauchySumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySumCarrier_zero_source_consumer_route [AskSetup] [PackageSetup]
    {a b wa wb da db d e r h c p n zeroSeed zeroWindow zeroRead zeroSeal sumRead consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySumCarrier a b wa wb da db d e r h c p n bundle pkg ->
      Cont zeroSeed zeroWindow zeroRead ->
        Cont zeroRead zeroSeal sumRead ->
          Cont r sumRead consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory zeroSeed ->
                UnaryHistory zeroWindow ->
                  UnaryHistory zeroSeal ->
                    UnaryHistory r ∧ UnaryHistory zeroRead ∧ UnaryHistory sumRead ∧
                      UnaryHistory consumer ∧ Cont zeroSeed zeroWindow zeroRead ∧
                        Cont zeroRead zeroSeal sumRead ∧ Cont r sumRead consumer ∧
                          PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier zeroRoute sealRoute consumerRoute consumerPkg zeroSeedUnary zeroWindowUnary
    zeroSealUnary
  obtain ⟨_aUnary, _bUnary, _waUnary, _wbUnary, daUnary, dbUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _waRoute, _wbRoute, sumRoute, readbackRoute, _provenanceRoute,
    pPkg⟩ := carrier
  have dUnary : UnaryHistory d :=
    unary_cont_closed daUnary dbUnary sumRoute
  have rUnary : UnaryHistory r :=
    unary_cont_closed dUnary eUnary readbackRoute
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroSeedUnary zeroWindowUnary zeroRoute
  have sumReadUnary : UnaryHistory sumRead :=
    unary_cont_closed zeroReadUnary zeroSealUnary sealRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed rUnary sumReadUnary consumerRoute
  exact
    ⟨rUnary, zeroReadUnary, sumReadUnary, consumerUnary, zeroRoute, sealRoute,
      consumerRoute, pPkg, consumerPkg⟩

end BEDC.Derived.RegularCauchySumUp
