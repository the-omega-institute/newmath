import BEDC.Derived.DiagonallimitrepresentativeUp

namespace BEDC.Derived.DiagonallimitrepresentativeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitRepresentativeFormalHandoffBoundary [AskSetup] [PackageSetup]
    {family modulus request selectedFamilyIndex selectedReadbackIndex window readback ledger
      realSeal transport continuation provenance localName indexRead terminalRead routeRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitRepresentativeCarrier family modulus request selectedFamilyIndex
        selectedReadbackIndex window readback ledger realSeal transport continuation provenance
        localName bundle pkg ->
      Cont modulus request indexRead ->
        Cont window readback terminalRead ->
          Cont ledger realSeal routeRead ->
            Cont routeRead continuation consumer ->
              PkgSig bundle consumer pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row family ∨ hsame row modulus ∨ hsame row request ∨
                        hsame row window ∨ hsame row readback ∨ hsame row ledger ∨
                          hsame row realSeal ∨ hsame row routeRead ∨ hsame row consumer)
                    (fun row : BHist =>
                      hsame row consumer ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle consumer pkg)
                    hsame ∧
                  UnaryHistory indexRead ∧ UnaryHistory terminalRead ∧ UnaryHistory routeRead ∧
                    UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier modulusRequestIndex windowReadbackTerminal ledgerSealRoute routeConsumer
    consumerPkg
  obtain ⟨familyUnary, modulusUnary, requestUnary, _selectedFamilyUnary,
    _selectedReadbackUnary, windowUnary, readbackUnary, ledgerUnary, realSealUnary,
    provenanceUnary, _localNameUnary, _modulusRequestSelected, _windowReadbackSelected,
    _ledgerSealTransport, transportContinuationProvenance, localPkg⟩ := carrier
  have indexUnary : UnaryHistory indexRead :=
    unary_cont_closed modulusUnary requestUnary modulusRequestIndex
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed windowUnary readbackUnary windowReadbackTerminal
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerSealRoute
  have continuationUnary : UnaryHistory continuation :=
    unary_cont_right_factor transportContinuationProvenance provenanceUnary
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary continuationUnary routeConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row family ∨ hsame row modulus ∨ hsame row request ∨
            hsame row window ∨ hsame row readback ∨ hsame row ledger ∨
              hsame row realSeal ∨ hsame row routeRead ∨ hsame row consumer)
        (fun row : BHist =>
          hsame row consumer ∧ PkgSig bundle localName pkg ∧
            PkgSig bundle consumer pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, localPkg, consumerPkg⟩
    }
  exact ⟨cert, indexUnary, terminalUnary, routeUnary, consumerUnary⟩

end BEDC.Derived.DiagonallimitrepresentativeUp
