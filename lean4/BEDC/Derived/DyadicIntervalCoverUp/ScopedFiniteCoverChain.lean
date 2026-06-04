import BEDC.Derived.DyadicIntervalCoverUp

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverScopedFiniteCoverChain [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead coverRead sealRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg) →
      Cont L U endpointRead →
        Cont W Q windowRead →
          Cont M R coverRead →
            Cont coverRead A sealRead →
              Cont sealRead N namedRead →
                PkgSig bundle namedRead pkg →
                  UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory coverRead ∧ UnaryHistory sealRead ∧
                      UnaryHistory namedRead ∧ Cont L U endpointRead ∧
                        Cont W Q windowRead ∧ Cont M R coverRead ∧
                          Cont coverRead A sealRead ∧ Cont sealRead N namedRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro surface endpointRoute windowRoute coverRoute sealRoute namedRoute namedPkg
  obtain ⟨unaryL, unaryU, unaryM, unaryR, _unaryV, unaryW, unaryQ, unaryA, _unaryH,
    _unaryC, _unaryP, unaryN, provenancePkg⟩ := surface
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed unaryL unaryU endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryQ windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed unaryM unaryR coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary unaryA sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  exact
    ⟨endpointUnary, windowUnary, coverUnary, sealUnary, namedUnary, endpointRoute,
      windowRoute, coverRoute, sealRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
