import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_generator_normalization_readiness [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert sigRead motiveRead branchRead descentRead outputRead normalized : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg ->
      Cont signature eliminator sigRead ->
        Cont sigRead motive motiveRead ->
          Cont motiveRead branch branchRead ->
            Cont branchRead descent descentRead ->
              Cont descentRead output outputRead ->
                Cont outputRead audit normalized ->
                  PkgSig bundle normalized pkg ->
                    UnaryHistory sigRead ∧ UnaryHistory motiveRead ∧
                      UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                        UnaryHistory outputRead ∧ UnaryHistory normalized ∧
                          Cont signature eliminator sigRead ∧ Cont sigRead motive motiveRead ∧
                            Cont motiveRead branch branchRead ∧
                              Cont branchRead descent descentRead ∧
                                Cont descentRead output outputRead ∧
                                  Cont outputRead audit normalized ∧
                                    hsame transport (append audit continuation) ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle normalized pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier signatureEliminatorSig sigMotiveRead motiveBranchRead branchDescentRead
    descentOutputRead outputAuditNormalized normalizedPkg
  rcases carrier with
    ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary, outputUnary,
      auditUnary, _transportUnary, _continuationUnary, _provenanceUnary, _boundaryUnary,
      _localCertUnary, _signatureEliminatorMotive, _motiveBranchDescent, _descentOutputAudit,
      transportAuditContinuation, provenancePkg⟩
  have sigReadUnary : UnaryHistory sigRead :=
    unary_cont_closed signatureUnary eliminatorUnary signatureEliminatorSig
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed sigReadUnary motiveUnary sigMotiveRead
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed motiveReadUnary branchUnary motiveBranchRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed branchReadUnary descentUnary branchDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary descentOutputRead
  have normalizedUnary : UnaryHistory normalized :=
    unary_cont_closed outputReadUnary auditUnary outputAuditNormalized
  exact
    ⟨sigReadUnary, motiveReadUnary, branchReadUnary, descentReadUnary, outputReadUnary,
      normalizedUnary, signatureEliminatorSig, sigMotiveRead, motiveBranchRead,
      branchDescentRead, descentOutputRead, outputAuditNormalized,
      transportAuditContinuation, provenancePkg, normalizedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
