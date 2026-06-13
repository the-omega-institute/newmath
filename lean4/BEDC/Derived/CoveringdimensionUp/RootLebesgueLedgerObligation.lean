import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootLebesgueLedgerObligation [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue transport replay provenance
      localName compactRead finiteRead ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        transport replay provenance localName bundle pkg →
      Cont compactMetric epsilonNet compactRead →
        Cont compactRead cover finiteRead →
          Cont finiteRead lebesgue ledgerRead →
            Cont ledgerRead localName namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row lebesgue ∨ hsame row ledgerRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compactMetric epsilonNet compactRead ∧
                        Cont compactRead cover finiteRead ∧
                          Cont finiteRead lebesgue ledgerRead ∧
                            Cont ledgerRead localName namedRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory compactRead ∧ UnaryHistory finiteRead ∧
                    UnaryHistory ledgerRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute finiteRoute ledgerRoute namedRoute namedPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, _refinementUnary, _orderUnary,
    lebesgueUnary, _transportUnary, _replayUnary, provenanceUnary, localNameUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReplay,
    _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactUnary epsilonUnary compactRoute
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed compactReadUnary coverUnary finiteRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed finiteReadUnary lebesgueUnary ledgerRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerReadUnary localNameUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, compactRoute, finiteRoute, ledgerRoute, namedRoute, provenancePkg,
            namedPkg⟩
    }
  · exact ⟨compactReadUnary, finiteReadUnary, ledgerReadUnary, namedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
