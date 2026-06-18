import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopCompletionComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopCompletionComparisonCarrier [AskSetup] [PackageSetup]
    (regular boundary located enclosure sealRow transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory regular ∧ UnaryHistory boundary ∧ UnaryHistory located ∧
    UnaryHistory enclosure ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem BishopCompletionComparisonCarrier_regular_located_route [AskSetup] [PackageSetup]
    {regular boundary located enclosure sealRow transport replay provenance localName midRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopCompletionComparisonCarrier regular boundary located enclosure sealRow transport replay
        provenance localName bundle pkg ->
      Cont regular boundary midRead ->
        Cont midRead located enclosure ->
          Cont enclosure sealRow sealRead ->
            PkgSig bundle provenance pkg ->
              PkgSig bundle localName pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
                        hsame row enclosure ∨ hsame row sealRow ∨ hsame row midRead ∨
                          hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont regular boundary midRead ∧
                        Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                          PkgSig bundle provenance pkg)
                    hsame ∧ Cont regular boundary midRead ∧ Cont midRead located enclosure ∧
                  Cont enclosure sealRow sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier regularBoundary midLocated enclosureSeal provenancePkg _localNamePkg
  obtain ⟨regularUnary, boundaryUnary, locatedUnary, _enclosureUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrier
  have midReadUnary : UnaryHistory midRead :=
    unary_cont_closed regularUnary boundaryUnary regularBoundary
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed midReadUnary locatedUnary midLocated
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureUnary sealUnary enclosureSeal
  have sealSource :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regular ∨ hsame row boundary ∨ hsame row located ∨
              hsame row enclosure ∨ hsame row sealRow ∨ hsame row midRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont regular boundary midRead ∧
              Cont midRead located enclosure ∧ Cont enclosure sealRow sealRead ∧
                PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sealRead sealSource
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
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro row sourceRow
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left)))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, regularBoundary, midLocated, enclosureSeal, provenancePkg⟩
    }
  exact ⟨cert, regularBoundary, midLocated, enclosureSeal⟩

end BEDC.Derived.BishopCompletionComparisonUp
