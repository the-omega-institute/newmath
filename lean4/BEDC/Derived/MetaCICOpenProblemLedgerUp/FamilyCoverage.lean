import BEDC.Derived.MetaCICOpenProblemLedgerUp

namespace BEDC.Derived.MetaCICOpenProblemLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICOpenProblemLedger_family_coverage [AskSetup] [PackageSetup]
    {S C N U D E B H R P Q familyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICOpenProblemLedgerCarrier S C N U D E B H R P Q bundle pkg ->
      Cont S C familyRead ->
        PkgSig bundle familyRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row familyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨
                  hsame row D ∨ hsame row E ∨ hsame row B ∨ hsame row familyRead)
              (fun row : BHist => hsame row familyRead ∧ PkgSig bundle familyRead pkg)
              hsame ∧
            UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory U ∧
              UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory B ∧
                UnaryHistory familyRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier familyRoute familyPkg
  obtain ⟨sUnary, cUnary, nUnary, uUnary, dUnary, eUnary, bUnary, _hUnary,
    _rUnary, _pUnary, _qUnary, _subjectConfluenceName, _substitutionDecidableExample,
    _blockerHandoffReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed sUnary cUnary familyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row familyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row C ∨ hsame row N ∨ hsame row U ∨
              hsame row D ∨ hsame row E ∨ hsame row B ∨ hsame row familyRead)
          (fun row : BHist => hsame row familyRead ∧ PkgSig bundle familyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro familyRead ⟨hsame_refl familyRead, familyUnary⟩
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
      exact ⟨source.left, familyPkg⟩
  }
  exact
    ⟨cert, sUnary, cUnary, nUnary, uUnary, dUnary, eUnary, bUnary, familyUnary⟩

end BEDC.Derived.MetaCICOpenProblemLedgerUp
