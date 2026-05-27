import BEDC.Derived.MetricCompletionUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionUp.SeparatedLimitBoundary

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

theorem MetricCompletion_separated_limit_uniqueness_boundary [AskSetup] [PackageSetup]
    {source filterBranch netBranch readback separated transport replay provenance localCert
      leftRead rightRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
        provenance localCert bundle pkg →
      Cont readback separated replay →
        hsame leftRead separated →
          hsame rightRead separated →
            Cont leftRead rightRead routeRead →
              PkgSig bundle routeRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row leftRead ∨ hsame row rightRead ∨ hsame row separated ∨
                        hsame row replay ∨ hsame row routeRead)
                    (fun row : BHist =>
                      hsame row routeRead ∧ PkgSig bundle routeRead pkg ∧
                        Cont readback separated replay)
                    hsame ∧
                  hsame leftRead rightRead ∧ UnaryHistory replay ∧
                    UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro carrier separatedRoute leftSame rightSame route pkgRoute
  obtain ⟨_sourceUnary, _filterUnary, _netUnary, readbackUnary, separatedUnary,
    _transportUnary, _replayUnaryCarrier, _provenanceUnary, _localCertUnary,
    _carrierReplayRoute, _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have leftUnary : UnaryHistory leftRead :=
    unary_transport_symm separatedUnary leftSame
  have rightUnary : UnaryHistory rightRead :=
    unary_transport_symm separatedUnary rightSame
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed leftUnary rightUnary route
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed readbackUnary separatedUnary separatedRoute
  have leftRight : hsame leftRead rightRead :=
    hsame_trans leftSame (hsame_symm rightSame)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row leftRead ∨ hsame row rightRead ∨ hsame row separated ∨
              hsame row replay ∨ hsame row routeRead)
          (fun row : BHist =>
            hsame row routeRead ∧ PkgSig bundle routeRead pkg ∧
              Cont readback separated replay)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgRoute, separatedRoute⟩
    }
  exact ⟨cert, leftRight, replayUnary, routeUnary⟩

end BEDC.Derived.MetricCompletionUp.SeparatedLimitBoundary
