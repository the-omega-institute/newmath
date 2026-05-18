import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBranchDescentLedger [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output audit transport continuation provenance
      boundary localCert branchRead descentRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier signature eliminator motive branch descent output audit
        transport continuation provenance boundary localCert bundle pkg →
      Cont motive branch descentRead →
        Cont branch descent branchRead →
          Cont descentRead output outputRead →
            PkgSig bundle outputRead pkg →
              UnaryHistory motive ∧ UnaryHistory branch ∧ UnaryHistory descent ∧
                UnaryHistory output ∧ UnaryHistory descentRead ∧ UnaryHistory branchRead ∧
                  UnaryHistory outputRead ∧ Cont signature eliminator motive ∧
                    Cont motive branch descentRead ∧ Cont branch descent branchRead ∧
                      Cont descentRead output outputRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier motiveBranchDescent branchDescentRead descentOutputRead outputPkg
  obtain ⟨_signatureUnary, _eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, _auditUnary, _transportUnary, _continuationUnary, _provenanceUnary,
    _boundaryUnary, _localCertUnary, signatureEliminatorMotive, _motiveBranchDescent,
    _descentOutputAudit, _transportSame, provenancePkg⟩ := carrier
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed motiveUnary branchUnary motiveBranchDescent
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchUnary descentUnary branchDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed descentReadUnary outputUnary descentOutputRead
  exact
    ⟨motiveUnary, branchUnary, descentUnary, outputUnary, descentReadUnary, branchReadUnary,
      outputReadUnary, signatureEliminatorMotive, motiveBranchDescent, branchDescentRead,
      descentOutputRead, provenancePkg, outputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
