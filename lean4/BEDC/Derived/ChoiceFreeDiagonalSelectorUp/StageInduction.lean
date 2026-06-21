import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.WindowRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp.StageInduction

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorCarrier_stage_induction [AskSetup] [PackageSetup]
    {eps windows stage readback sealRow transport replay provenance localName stageRead nextRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory eps ->
      UnaryHistory windows ->
        UnaryHistory stage ->
          UnaryHistory readback ->
            UnaryHistory sealRow ->
              Cont eps windows stageRead ->
                Cont stageRead stage nextRead ->
                  PkgSig bundle provenance pkg ->
                    PkgSig bundle localName pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row nextRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row eps ∨ hsame row windows ∨ hsame row stage ∨
                              hsame row nextRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont eps windows stageRead ∧
                              Cont stageRead stage nextRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle localName pkg)
                          hsame ∧ UnaryHistory stageRead ∧ UnaryHistory nextRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro epsUnary windowsUnary stageUnary _readbackUnary _sealUnary epsWindows stageRoute
    provenancePkg localNamePkg
  have stageReadUnary : UnaryHistory stageRead :=
    unary_cont_closed epsUnary windowsUnary epsWindows
  have nextReadUnary : UnaryHistory nextRead :=
    unary_cont_closed stageReadUnary stageUnary stageRoute
  have sourceNext :
      (fun row : BHist => hsame row nextRead ∧ UnaryHistory row) nextRead := by
    exact ⟨hsame_refl nextRead, nextReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nextRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row eps ∨ hsame row windows ∨ hsame row stage ∨ hsame row nextRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont eps windows stageRead ∧ Cont stageRead stage nextRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nextRead sourceNext
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
        constructor
        · exact hsame_trans (hsame_symm sameRows) sourceRow.left
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, epsWindows, stageRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, stageReadUnary, nextReadUnary⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp.StageInduction
