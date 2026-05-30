import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.BranchInterfaceScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

def MetricCompletionBranchInterfaceScope [AskSetup] [PackageSetup]
    (source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead readbackRead separatedRead scopeRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
      provenance localCert bundle pkg ∧
    (hsame selectedBranch filterBranch ∨ hsame selectedBranch netBranch) ∧
      Cont source selectedBranch branchRead ∧ Cont branchRead readback readbackRead ∧
        Cont readbackRead separated separatedRead ∧ Cont separatedRead replay scopeRead ∧
          PkgSig bundle scopeRead pkg

theorem MetricCompletionBranchInterfaceScope_route_certificate [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      selectedBranch branchRead readbackRead separatedRead scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionBranchInterfaceScope source filterBranch netBranch readback separated
        transport replay provenance localCert selectedBranch branchRead readbackRead
        separatedRead scopeRead bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readbackRead ∨ hsame row separatedRead ∨ hsame row scopeRead)
          (fun row : BHist => hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory selectedBranch ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro scope
  obtain ⟨carrier, selectedCases, sourceSelectedBranch, branchReadReadback,
    readbackSeparated, separatedReplay, scopePkg⟩ := scope
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedBranch := by
    cases selectedCases with
    | inl sameFilter =>
        exact unary_transport filterUnary (hsame_symm sameFilter)
    | inr sameNet =>
        exact unary_transport netUnary (hsame_symm sameNet)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed sourceUnary selectedUnary sourceSelectedBranch
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed branchReadUnary readbackUnary branchReadReadback
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed readbackReadUnary separatedUnary readbackSeparated
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed separatedReadUnary replayUnary separatedReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row selectedBranch ∨ hsame row branchRead ∨
              hsame row readbackRead ∨ hsame row separatedRead ∨ hsame row scopeRead)
          (fun row : BHist => hsame row scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopeReadUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, scopePkg⟩
    }
  exact ⟨cert, sourceUnary, selectedUnary, scopeReadUnary⟩

end BEDC.Derived.MetricCompletionUp.BranchInterfaceScope
