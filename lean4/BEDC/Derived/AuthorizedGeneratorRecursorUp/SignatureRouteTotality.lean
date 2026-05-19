import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorSignatureRouteTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N signatureRead descentRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E signatureRead ->
        Cont B D descentRead ->
          Cont descentRead O outputRead ->
            PkgSig bundle outputRead pkg ->
              UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧
                  UnaryHistory signatureRead ∧ UnaryHistory descentRead ∧
                    UnaryHistory outputRead ∧ Cont I E signatureRead ∧
                      Cont B D descentRead ∧ Cont descentRead O outputRead ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier signatureCont descentCont outputCont outputPkg
  obtain ⟨iUnary, eUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
    auditUnary, _transportUnary, continuationUnary, _provenanceUnary, _boundaryUnary,
    _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, transportAuditContinuation, provenancePkg⟩ := carrier
  have signatureReadUnary : UnaryHistory signatureRead :=
    unary_cont_closed iUnary eUnary signatureCont
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary descentUnary descentCont
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary outputCont
  exact
    ⟨iUnary, eUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, signatureReadUnary, descentReadUnary, outputReadUnary, signatureCont,
      descentCont, outputCont, transportAuditContinuation, provenancePkg, outputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
