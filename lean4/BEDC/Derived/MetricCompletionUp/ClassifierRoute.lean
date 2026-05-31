import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.ClassifierRoute

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

def MetricCompletionClassifier [AskSetup] [PackageSetup]
    (source filterBranch netBranch readback separated transport replay provenance localCert
      leftRead rightRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
      provenance localCert bundle pkg ∧
    (hsame leftRead source ∨ hsame leftRead filterBranch ∨ hsame leftRead netBranch ∨
      hsame leftRead readback ∨ hsame leftRead separated) ∧
      (hsame rightRead source ∨ hsame rightRead filterBranch ∨ hsame rightRead netBranch ∨
        hsame rightRead readback ∨ hsame rightRead separated) ∧
        hsame transport provenance ∧ PkgSig bundle localCert pkg

theorem MetricCompletionClassifier_route_certificate [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      leftRead rightRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionClassifier source filterBranch netBranch readback separated transport replay
        provenance localCert leftRead rightRead bundle pkg →
      Cont leftRead rightRead classifierRead →
        PkgSig bundle classifierRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row filterBranch ∨ hsame row netBranch ∨
                  hsame row readback ∨ hsame row separated ∨ hsame row classifierRead)
              (fun row : BHist => hsame row classifierRead ∧ PkgSig bundle classifierRead pkg)
              hsame ∧
            UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro classifier classifierRoute classifierPkg
  obtain ⟨carrier, leftCases, rightCases, _transportSame, _localCertPkg⟩ := classifier
  obtain ⟨sourceUnary, filterUnary, netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _replayRoute,
    _carrierTransportSame, _provenancePkg, _carrierLocalCertPkg⟩ := carrier
  have leftUnary : UnaryHistory leftRead := by
    cases leftCases with
    | inl sameSource =>
        exact unary_transport sourceUnary (hsame_symm sameSource)
    | inr rest =>
        cases rest with
        | inl sameFilter =>
            exact unary_transport filterUnary (hsame_symm sameFilter)
        | inr rest =>
            cases rest with
            | inl sameNet =>
                exact unary_transport netUnary (hsame_symm sameNet)
            | inr rest =>
                cases rest with
                | inl sameReadback =>
                    exact unary_transport readbackUnary (hsame_symm sameReadback)
                | inr sameSeparated =>
                    exact unary_transport separatedUnary (hsame_symm sameSeparated)
  have rightUnary : UnaryHistory rightRead := by
    cases rightCases with
    | inl sameSource =>
        exact unary_transport sourceUnary (hsame_symm sameSource)
    | inr rest =>
        cases rest with
        | inl sameFilter =>
            exact unary_transport filterUnary (hsame_symm sameFilter)
        | inr rest =>
            cases rest with
            | inl sameNet =>
                exact unary_transport netUnary (hsame_symm sameNet)
            | inr rest =>
                cases rest with
                | inl sameReadback =>
                    exact unary_transport readbackUnary (hsame_symm sameReadback)
                | inr sameSeparated =>
                    exact unary_transport separatedUnary (hsame_symm sameSeparated)
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed leftUnary rightUnary classifierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row filterBranch ∨ hsame row netBranch ∨
              hsame row readback ∨ hsame row separated ∨ hsame row classifierRead)
          (fun row : BHist => hsame row classifierRead ∧ PkgSig bundle classifierRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro classifierRead ⟨hsame_refl classifierRead, classifierUnary⟩
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
        exact ⟨sourceRow.left, classifierPkg⟩
    }
  exact ⟨cert, classifierUnary⟩

end BEDC.Derived.MetricCompletionUp.ClassifierRoute
