import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBranchDescentTotality [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont motive branch branchRead ->
        Cont descent output auditRead ->
          PkgSig bundle auditRead pkg ->
            UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory branchRead ∧
              UnaryHistory auditRead ∧ Cont signature eliminator motive ∧
                Cont motive branch branchRead ∧ Cont descent output auditRead ∧
                  hsame transport (append audit continuation) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier motiveBranchRead descentOutputRead auditReadPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, sameTransport, provenancePkg⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveUnary branchUnary motiveBranchRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  exact
    ⟨branchUnary, descentUnary, branchReadUnary, auditReadUnary, signatureEliminatorMotive,
      motiveBranchRead, descentOutputRead, sameTransport, provenancePkg, auditReadPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
