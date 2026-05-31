import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.CompletionConsumerTotality

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_completion_consumer_totality [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead toleranceRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) →
        Cont source selectedBranch branchRead →
          Cont branchRead readback toleranceRead →
            Cont toleranceRead separated sealedRead →
              PkgSig bundle sealedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
                        hsame row toleranceRead ∨ hsame row separated ∨ hsame row sealedRead)
                    (fun row : BHist => hsame row sealedRead ∧ PkgSig bundle sealedRead pkg)
                    hsame ∧
                  UnaryHistory source ∧ UnaryHistory selectedBranch ∧
                    UnaryHistory branchRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory sealedRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle sealedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier branchChoice branchRoute toleranceRoute sealedRoute sealedPkg
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _carrierReplay,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases branchChoice with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary branchRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed branchReadUnary readbackUnary toleranceRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed toleranceUnary separatedUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row toleranceRead ∨ hsame row separated ∨ hsame row sealedRead)
          (fun row : BHist => hsame row sealedRead ∧ PkgSig bundle sealedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows sourceRow
          constructor
          · exact hsame_trans (hsame_symm sameRows) sourceRow.left
          · exact unary_transport sourceRow.right sameRows
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, sealedPkg⟩
    }
  exact
    ⟨cert, sourceUnary, selectedUnary, branchReadUnary, toleranceUnary, sealedUnary,
      provenancePkg, sealedPkg⟩

end BEDC.Derived.MetricCompletionUp.CompletionConsumerTotality
