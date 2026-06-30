import BEDC.Derived.BishopCompletionComparisonUp.RealRoute

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionComparisonCarrier_boundary_transport [AskSetup] [PackageSetup]
    {regular boundary located enclosure sealRow transport replay provenance localName midRead
      sealRead auditRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionComparisonCarrier regular boundary located enclosure sealRow transport replay
        provenance localName bundle pkg →
      Cont regular boundary midRead →
        Cont midRead located enclosure →
          Cont enclosure sealRow sealRead →
            Cont provenance localName auditRead →
              Cont auditRead sealRow realRead →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
                          hsame row enclosure ∨ hsame row sealRow ∨ hsame row transport ∨
                            hsame row replay ∨ hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont regular boundary midRead ∧
                          Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                            PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory midRead ∧ UnaryHistory sealRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier regularBoundary midLocated enclosureSeal provenanceAudit auditReal realPkg
  obtain ⟨regularUnary, boundaryUnary, locatedUnary, _enclosureUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have midReadUnary : UnaryHistory midRead :=
    unary_cont_closed regularUnary boundaryUnary regularBoundary
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed midReadUnary locatedUnary midLocated
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureUnary sealUnary enclosureSeal
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
                hsame row replay ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regular boundary midRead ∧
              Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                PkgSig bundle realRead pkg)
          hsame := {
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, regularBoundary, midLocated, enclosureSeal, realPkg⟩
  }
  exact ⟨cert, midReadUnary, sealReadUnary, realReadUnary⟩

end BEDC.Derived.BishopCompletionComparisonUp
