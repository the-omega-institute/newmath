import BEDC.Derived.ChoiceRecipeLedgerUp

namespace BEDC.Derived.ChoiceRecipeLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceRecipeLedgerCarrier_mature_package [AskSetup] [PackageSetup]
    {request recipes output refusal transport route provenance localName obligationRead
      coverageRead accountabilityRead replacement handoff publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceRecipeLedgerCarrier request recipes output refusal transport route provenance localName
        bundle pkg ->
      Cont provenance localName obligationRead ->
        Cont recipes refusal coverageRead ->
          Cont request output accountabilityRead ->
            Cont output refusal replacement ->
              Cont localName request handoff ->
                Cont handoff obligationRead publicRead ->
                  PkgSig bundle obligationRead pkg ->
                    PkgSig bundle coverageRead pkg ->
                      PkgSig bundle accountabilityRead pkg ->
                        PkgSig bundle replacement pkg ->
                          PkgSig bundle handoff pkg ->
                            PkgSig bundle publicRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row publicRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row request ∨ hsame row recipes ∨
                                      hsame row output ∨ hsame row refusal ∨
                                        hsame row obligationRead ∨ hsame row coverageRead ∨
                                          hsame row accountabilityRead ∨
                                            hsame row replacement ∨ hsame row handoff ∨
                                              hsame row publicRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
                                      Cont handoff obligationRead publicRead)
                                  hsame ∧
                                UnaryHistory request ∧ UnaryHistory recipes ∧
                                  UnaryHistory output ∧ UnaryHistory refusal ∧
                                    UnaryHistory publicRead ∧ PkgSig bundle localName pkg ∧
                                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro carrier provenanceLocalName recipesRefusalCoverage requestOutputAccountability
    outputRefusalReplacement localNameRequest handoffObligation _obligationPkg _coveragePkg
    _accountabilityPkg _replacementPkg _handoffPkg publicPkg
  obtain ⟨requestUnary, recipesUnary, outputUnary, refusalUnary, _transportUnary, _routeUnary,
    provenanceUnary, localNameUnary, _requestRecipesOutput, _outputRefusalRoute,
    _routeTransportProvenance, localNamePkg⟩ := carrier
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocalName
  have _coverageUnary : UnaryHistory coverageRead :=
    unary_cont_closed recipesUnary refusalUnary recipesRefusalCoverage
  have _accountabilityUnary : UnaryHistory accountabilityRead :=
    unary_cont_closed requestUnary outputUnary requestOutputAccountability
  have _replacementUnary : UnaryHistory replacement :=
    unary_cont_closed outputUnary refusalUnary outputRefusalReplacement
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed localNameUnary requestUnary localNameRequest
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed handoffUnary obligationUnary handoffObligation
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row request ∨ hsame row recipes ∨ hsame row output ∨
              hsame row refusal ∨ hsame row obligationRead ∨ hsame row coverageRead ∨
                hsame row accountabilityRead ∨ hsame row replacement ∨
                  hsame row handoff ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
              Cont handoff obligationRead publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
                      (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg, handoffObligation⟩
  }
  exact
    ⟨cert, requestUnary, recipesUnary, outputUnary, refusalUnary, publicUnary, localNamePkg,
      publicPkg⟩

end BEDC.Derived.ChoiceRecipeLedgerUp
