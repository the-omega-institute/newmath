import BEDC.Derived.BishopCompletionComparisonUp.RegularLocatedRoute

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionComparisonRegularSeal [AskSetup] [PackageSetup]
    {regular boundary located enclosure sealRow transport replay provenance localName midRead
      sealRead regularSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionComparisonCarrier regular boundary located enclosure sealRow transport replay
        provenance localName bundle pkg →
      Cont regular boundary midRead →
        Cont midRead located enclosure →
          Cont enclosure sealRow sealRead →
            Cont sealRead localName regularSeal →
              PkgSig bundle regularSeal pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row regularSeal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
                        hsame row enclosure ∨ hsame row sealRow ∨ hsame row midRead ∨
                          hsame row sealRead ∨ hsame row regularSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont regular boundary midRead ∧
                        Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                          Cont sealRead localName regularSeal ∧
                            PkgSig bundle regularSeal pkg)
                    hsame ∧
                  UnaryHistory regularSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier regularBoundary midLocated enclosureSeal sealLocal regularSealPkg
  obtain ⟨regularUnary, boundaryUnary, locatedUnary, _enclosureUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have midReadUnary : UnaryHistory midRead :=
    unary_cont_closed regularUnary boundaryUnary regularBoundary
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed midReadUnary locatedUnary midLocated
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureUnary sealUnary enclosureSeal
  have regularSealUnary : UnaryHistory regularSeal :=
    unary_cont_closed sealReadUnary localNameUnary sealLocal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row regularSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
              hsame row enclosure ∨ hsame row sealRow ∨ hsame row midRead ∨
                hsame row sealRead ∨ hsame row regularSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regular boundary midRead ∧
              Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                Cont sealRead localName regularSeal ∧ PkgSig bundle regularSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro regularSeal ⟨hsame_refl regularSeal, regularSealUnary⟩
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
      exact
        ⟨source.right, regularBoundary, midLocated, enclosureSeal, sealLocal,
          regularSealPkg⟩
  }
  exact ⟨cert, regularSealUnary⟩

end BEDC.Derived.BishopCompletionComparisonUp
