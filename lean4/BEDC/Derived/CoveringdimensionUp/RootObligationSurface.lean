import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootObligationSurface [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead refinementRead lebesgueRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead refinement refinementRead →
          Cont refinementRead lebesgue lebesgueRead →
            Cont lebesgueRead localName namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨ hsame row lebesgue ∨
                          hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory compactRead ∧ UnaryHistory refinementRead ∧
                    UnaryHistory lebesgueRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier compactRoute refinementRoute lebesgueRoute namedRoute namedPkg
  obtain ⟨compactUnary, epsilonUnary, _coverUnary, refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed compactReadUnary refinementUnary refinementRoute
  have lebesgueReadUnary : UnaryHistory lebesgueRead :=
    unary_cont_closed refinementReadUnary lebesgueUnary lebesgueRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed lebesgueReadUnary localNameUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
          intro row other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))
      ledger_sound := by
        intro row source
        exact ⟨source.right, provenancePkg, namedPkg⟩
    }
  · exact ⟨compactReadUnary, refinementReadUnary, lebesgueReadUnary, namedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
