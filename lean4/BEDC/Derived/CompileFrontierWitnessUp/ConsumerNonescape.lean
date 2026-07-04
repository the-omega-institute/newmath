import BEDC.Derived.CompileFrontierWitnessUp

namespace BEDC.Derived.CompileFrontierWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompileFrontierWitnessCarrier_consumer_nonescape [AskSetup] [PackageSetup]
    {F T S A B H C P N stageRead auditRead boundaryRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompileFrontierWitnessCarrier F T S A B H C P N bundle pkg ->
      Cont F S stageRead ->
        Cont stageRead A auditRead ->
          Cont auditRead B boundaryRead ->
            Cont boundaryRead C publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory stageRead ∧ UnaryHistory auditRead ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory publicRead ∧
                    Cont F S stageRead ∧ Cont stageRead A auditRead ∧
                      Cont auditRead B boundaryRead ∧ Cont boundaryRead C publicRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: CompileFrontierWitnessCarrier BHist Cont PkgSig UnaryHistory
  intro carrier stageRoute auditRoute boundaryRoute publicRoute publicPkg
  obtain ⟨unaryF, _unaryT, unaryS, unaryA, unaryB, _unaryH, unaryC, _unaryP,
    _unaryN, provenancePkg, _namePkg⟩ := carrier
  have stageReadUnary : UnaryHistory stageRead :=
    unary_cont_closed unaryF unaryS stageRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed stageReadUnary unaryA auditRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed auditReadUnary unaryB boundaryRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed boundaryReadUnary unaryC publicRoute
  exact
    ⟨stageReadUnary, auditReadUnary, boundaryReadUnary, publicReadUnary, stageRoute,
      auditRoute, boundaryRoute, publicRoute, provenancePkg, publicPkg⟩

end BEDC.Derived.CompileFrontierWitnessUp
