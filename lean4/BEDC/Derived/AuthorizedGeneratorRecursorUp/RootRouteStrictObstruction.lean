import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootRouteStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N carrierRead ledgerRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont A G carrierRead →
        PkgSig bundle carrierRead pkg →
          Cont G N ledgerRead →
            Cont ledgerRead A obstructionRead →
              UnaryHistory carrierRead ∧ UnaryHistory ledgerRead ∧
                UnaryHistory obstructionRead ∧ Cont A G carrierRead ∧
                  Cont G N ledgerRead ∧ Cont ledgerRead A obstructionRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle carrierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier auditBoundary carrierPkg boundaryLocal ledgerAudit
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, unaryN, _rootMotive, _branchDescent, _descentAudit,
      transportSame, packagePkg⟩
  have carrierUnary : UnaryHistory carrierRead :=
    unary_cont_closed unaryA unaryG auditBoundary
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryG unaryN boundaryLocal
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed ledgerUnary unaryA ledgerAudit
  exact
    ⟨carrierUnary, ledgerUnary, obstructionUnary, auditBoundary, boundaryLocal,
      ledgerAudit, transportSame, packagePkg, carrierPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
