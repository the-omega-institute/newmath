import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_public_citation_selector_exclusion
    [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow publicRead selectorRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont route provenance publicRead →
        Cont publicRead nameRow selectorRead →
          PkgSig bundle selectorRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row selectorRead ∧ Cont route provenance publicRead ∧
                    Cont publicRead nameRow selectorRead)
                (fun row : BHist => hsame row selectorRead ∧ PkgSig bundle selectorRead pkg)
                hsame ∧
              UnaryHistory selectorRead := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceRead publicNameSelector selectorPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, _provenancePkg⟩ :=
    carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceRead
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed publicReadUnary nameRowUnary publicNameSelector
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row selectorRead ∧ Cont route provenance publicRead ∧
              Cont publicRead nameRow selectorRead)
          (fun row : BHist => hsame row selectorRead ∧ PkgSig bundle selectorRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro selectorRead ⟨hsame_refl selectorRead, selectorReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, routeProvenanceRead, publicNameSelector⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, selectorPkg⟩
    }
  exact ⟨cert, selectorReadUnary⟩

end BEDC.Derived.ApophaticNameUp
