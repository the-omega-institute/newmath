import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTotalHostDecisionRouteExhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name decision : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal decision →
        PkgSig bundle decision pkg →
          SemanticNameCert
              (fun row : BHist => hsame row decision ∧ UnaryHistory row)
              (fun _row : BHist => Cont terminal normal decision ∧ PkgSig bundle decision pkg)
              (fun row : BHist => hsame row decision ∧ PkgSig bundle decision pkg)
              hsame ∧
            UnaryHistory decision ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet terminalNormalDecision decisionPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed terminalUnary normalUnary terminalNormalDecision
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro decision (And.intro (hsame_refl decision) decisionUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row _source
        exact ⟨terminalNormalDecision, decisionPkg⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, decisionPkg⟩
    }
  · exact ⟨decisionUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
