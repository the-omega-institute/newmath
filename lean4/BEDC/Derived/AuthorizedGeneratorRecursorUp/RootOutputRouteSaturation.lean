import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_root_output_route_saturation [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead descentRead outputRead publicRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont branch descent branchRead ->
        Cont motive descent descentRead ->
          Cont branchRead descentRead outputRead ->
            Cont outputRead continuation publicRead ->
              Cont output audit auditRead ->
                UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                  UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                    UnaryHistory auditRead ∧ hsame transport (append audit continuation) ∧
                      Cont branch descent branchRead ∧ Cont motive descent descentRead ∧
                        Cont branchRead descentRead outputRead ∧
                          Cont outputRead continuation publicRead ∧
                            Cont output audit auditRead ∧
                              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier branchRoute descentRoute outputRoute publicRoute auditRoute
  rcases carrier with
    ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
      outputUnary, auditUnary, _transportUnary, continuationUnary, _provenanceUnary,
      _boundaryUnary, _localCertUnary, _signatureEliminatorMotive,
      _motiveBranchDescent, _descentOutputAudit, transportSame, provenancePkg⟩
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed motiveUnary descentUnary descentRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed branchReadUnary descentReadUnary outputRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary continuationUnary publicRoute
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputUnary auditUnary auditRoute
  exact
    ⟨branchReadUnary, descentReadUnary, outputReadUnary, publicReadUnary,
      auditReadUnary, transportSame, branchRoute, descentRoute, outputRoute, publicRoute,
      auditRoute, provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
