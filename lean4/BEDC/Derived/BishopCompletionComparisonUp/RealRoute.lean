import BEDC.Derived.BishopCompletionComparisonUp.RegularLocatedRoute

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionComparisonCarrier_real_route [AskSetup] [PackageSetup]
    {regular boundary located enclosure sealRow transport replay provenance localName auditRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionComparisonCarrier regular boundary located enclosure sealRow transport replay
        provenance localName bundle pkg ->
      Cont transport replay provenance ->
        Cont provenance localName auditRead ->
          Cont auditRead sealRow realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
                      hsame row enclosure ∨ hsame row sealRow ∨ hsame row transport ∨
                        hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                          hsame row realRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont transport replay provenance ∧
                      Cont provenance localName auditRead ∧ Cont auditRead sealRow realRead ∧
                        PkgSig bundle realRead pkg)
                  hsame ∧
                UnaryHistory auditRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier transportReplay provenanceAudit auditReal realPkg
  obtain ⟨_regularUnary, _boundaryUnary, _locatedUnary, _enclosureUnary, sealUnary,
    transportUnary, replayUnary, provenanceUnary, localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have provenanceUnaryFromRoute : UnaryHistory provenance :=
    unary_cont_closed transportUnary replayUnary transportReplay
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceAudit
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed auditReadUnary sealUnary auditReal
  have realSource :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
              hsame row enclosure ∨ hsame row sealRow ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont transport replay provenance ∧
              Cont provenance localName auditRead ∧ Cont auditRead sealRow realRead ∧
                PkgSig bundle realRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realRead realSource
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
        exact ⟨source.right, transportReplay, provenanceAudit, auditReal, realPkg⟩
    }
  exact ⟨cert, auditReadUnary, realReadUnary⟩

end BEDC.Derived.BishopCompletionComparisonUp
