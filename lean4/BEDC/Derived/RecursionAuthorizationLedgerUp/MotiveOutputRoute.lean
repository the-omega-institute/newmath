import BEDC.Derived.RecursionAuthorizationLedgerUp.Carrier

namespace BEDC.Derived.RecursionAuthorizationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RecursionAuthorizationLedgerMotiveOutputRoute [AskSetup] [PackageSetup]
    {signature recursor motive branches descent output transport routes provenance name
      motiveRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature recursor motive branches descent output
        transport routes provenance name bundle pkg →
      Cont motive output motiveRead →
        Cont motiveRead routes outputRead →
          PkgSig bundle outputRead pkg →
            UnaryHistory signature ∧ UnaryHistory recursor ∧ UnaryHistory motive ∧
              UnaryHistory output ∧ UnaryHistory motiveRead ∧ UnaryHistory outputRead ∧
                Cont signature recursor motive ∧ Cont branches descent output ∧
                  Cont motive output motiveRead ∧ Cont motiveRead routes outputRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier motiveOutputRead motiveReadRoutesOutputRead outputReadPkg
  obtain ⟨signatureUnary, recursorUnary, motiveUnary, _branchesUnary, _descentUnary,
    outputUnary, _transportUnary, routesUnary, _provenanceUnary, _nameUnary,
    signatureRecursorMotive, branchesDescentOutput, _outputTransportRoutes,
    _transportRoutesProvenance, provenancePkg, _namePkg, _signatureCert⟩ :=
    carrier
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed motiveUnary outputUnary motiveOutputRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed motiveReadUnary routesUnary motiveReadRoutesOutputRead
  exact
    ⟨signatureUnary, recursorUnary, motiveUnary, outputUnary, motiveReadUnary,
      outputReadUnary, signatureRecursorMotive, branchesDescentOutput, motiveOutputRead,
      motiveReadRoutesOutputRead, provenancePkg, outputReadPkg⟩

end BEDC.Derived.RecursionAuthorizationLedgerUp
