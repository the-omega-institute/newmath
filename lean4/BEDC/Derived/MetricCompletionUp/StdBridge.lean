import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletionUp_StdBridge [AskSetup] [PackageSetup]
    {metricCauchy denseEmbedding completionSeal universalRoute separatedRow transport replay
      provenance localName bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier metricCauchy denseEmbedding completionSeal universalRoute separatedRow
        transport replay provenance localName bundle pkg →
      Cont universalRoute localName bridgeRead →
        PkgSig bundle bridgeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metricCauchy ∨ hsame row denseEmbedding ∨ hsame row completionSeal ∨
                  hsame row universalRoute ∨ hsame row bridgeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle bridgeRead pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont UnaryHistory
  intro carrier bridgeRoute bridgePkg
  obtain ⟨_metricUnary, _denseUnary, _sealUnary, routeUnary, _separatedUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localUnary, _replayRoute,
    _transportSame, provenancePkg, _localPkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed routeUnary localUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metricCauchy ∨ hsame row denseEmbedding ∨ hsame row completionSeal ∨
              hsame row universalRoute ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle bridgeRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, bridgePkg, provenancePkg⟩
    }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.MetricCompletionUp
