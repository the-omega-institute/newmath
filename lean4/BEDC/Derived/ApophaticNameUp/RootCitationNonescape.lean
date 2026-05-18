import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_root_citation_nonescape [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont route provenance citationRead ->
        PkgSig bundle citationRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg ∧ hsame row citationRead)
              (fun row : BHist =>
                hsame row socket ∨ hsame row request ∨ hsame row gate ∨
                  hsame row ledger ∨ hsame row citationRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle citationRead pkg ∧
                  hsame row citationRead)
              hsame ∧
            UnaryHistory citationRead ∧
            Cont route provenance citationRead ∧
            PkgSig bundle provenance pkg ∧
            PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenanceCitation citationPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have citationUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg ∧ hsame row citationRead)
          (fun row : BHist =>
            hsame row socket ∨ hsame row request ∨ hsame row gate ∨
              hsame row ledger ∨ hsame row citationRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle citationRead pkg ∧
              hsame row citationRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro citationRead
          ⟨carrierPacket, hsame_refl citationRead⟩
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
          exact ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.right)))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨provenancePkg, citationPkg, sourceRow.right⟩
    }
  exact ⟨cert, citationUnary, routeProvenanceCitation, provenancePkg, citationPkg⟩

end BEDC.Derived.ApophaticNameUp
