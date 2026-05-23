import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegSeqRatFiniteRequestSourceSection [AskSetup] [PackageSetup]
    {schedule index endpoint radius regularity provenance readback requestSection : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegSeqRatStreamCarrier schedule index endpoint radius regularity provenance readback
        bundle pkg ->
      Cont schedule endpoint requestSection ->
        PkgSig bundle requestSection pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row requestSection ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row schedule ∨ hsame row endpoint ∨ hsame row radius ∨
                hsame row regularity ∨ hsame row readback ∨ hsame row requestSection)
            (fun row : BHist =>
              hsame row requestSection ∧ PkgSig bundle requestSection pkg ∧
                Cont schedule endpoint requestSection)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sectionRoute sectionPkg
  have sectionUnary : UnaryHistory requestSection :=
    unary_cont_closed carrier.left carrier.right.right.left sectionRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro requestSection ⟨hsame_refl requestSection, sectionUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        exact ⟨hsame_trans (hsame_symm same) sourceRow.left,
          unary_transport sourceRow.right same⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sectionPkg, sectionRoute⟩
  }

end BEDC.Derived.RegSeqRatUp
