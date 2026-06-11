import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionCauchyForwardLink [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead cauchyWindow regSeqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead lebesgue cauchyWindow →
          Cont cauchyWindow replay regSeqRead →
            Cont regSeqRead transport realRead →
              PkgSig bundle realRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨
                        hsame row compactRead ∨ hsame row cover ∨ hsame row refinement ∨
                          hsame row orderBound ∨ hsame row lebesgue ∨
                            hsame row cauchyWindow ∨ hsame row regSeqRead ∨
                              hsame row realRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
                        Cont compactRead lebesgue cauchyWindow ∧
                          Cont cauchyWindow replay regSeqRead ∧
                            Cont regSeqRead transport realRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg)
                    hsame ∧
                  UnaryHistory compactRead ∧ UnaryHistory cauchyWindow ∧
                    UnaryHistory regSeqRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute cauchyRoute regSeqRoute realRoute realPkg
  obtain ⟨compactUnary, epsilonUnary, _coverUnary, _refinementUnary, _orderUnary,
    lebesgueUnary, transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactRoute
  have cauchyWindowUnary : UnaryHistory cauchyWindow :=
    unary_cont_closed compactReadUnary lebesgueUnary cauchyRoute
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed cauchyWindowUnary replayUnary regSeqRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqReadUnary transportUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row compactRead ∨
              hsame row cover ∨ hsame row refinement ∨ hsame row orderBound ∨
                hsame row lebesgue ∨ hsame row cauchyWindow ∨ hsame row regSeqRead ∨
                  hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
              Cont compactRead lebesgue cauchyWindow ∧
                Cont cauchyWindow replay regSeqRead ∧ Cont regSeqRead transport realRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, cauchyRoute, regSeqRoute, realRoute,
          provenancePkg, realPkg⟩
  }
  exact ⟨cert, compactReadUnary, cauchyWindowUnary, regSeqReadUnary, realReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
