import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorAcceptedSignatureRoute [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont descent output publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
            UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory publicRead ∧ Cont signature eliminator motive ∧
                Cont motive branch descent ∧ Cont descent output publicRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier descentOutputRead publicPkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary, _boundaryUnary,
      _localCertUnary, signatureEliminatorMotive, motiveBranchDescent, _descentOutputAudit,
      _sameTransport, provenancePkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed descentUnary outputUnary descentOutputRead
  exact
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      publicUnary, signatureEliminatorMotive, motiveBranchDescent, descentOutputRead,
      provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
