import BEDC.Derived.RealCompletionSelectorSealUp

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionSelectorSealRouteDeterminacy [AskSetup] [PackageSetup]
    {b w r l e h c p n h' c' n' terminal terminal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ->
      RealCompletionSelectorSealCarrier b w r l e h' c' p n' bundle pkg ->
        hsame c c' ->
          hsame n n' ->
            Cont e c terminal ->
              Cont e c' terminal' ->
                PkgSig bundle terminal pkg ->
                  PkgSig bundle terminal' pkg ->
                    hsame terminal terminal' ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle terminal pkg ∧ PkgSig bundle terminal' pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
                          (fun row : BHist => Cont e c row ∧ Cont b w r ∧ Cont r l e)
                          (fun row : BHist =>
                            hsame row terminal ∧ PkgSig bundle terminal pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier carrier' sameConsumer _sameName terminalRead terminalRead' terminalPkg
    terminalPkg'
  have bUnary : UnaryHistory b := carrier.left
  have wUnary : UnaryHistory w := carrier.right.left
  have rUnary : UnaryHistory r := carrier.right.right.left
  have lUnary : UnaryHistory l := carrier.right.right.right.left
  have eUnary : UnaryHistory e := carrier.right.right.right.right.left
  have cUnary : UnaryHistory c := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have bwr : Cont b w r := carrier.right.right.right.right.right.right.right.right.right.left
  have rle : Cont r l e := carrier.right.right.right.right.right.right.right.right.right.right.left
  have cUnary' : UnaryHistory c' := carrier'.right.right.right.right.right.right.left
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed eUnary cUnary terminalRead
  have sameTerminal : hsame terminal terminal' :=
    cont_respects_hsame (hsame_refl e) sameConsumer terminalRead terminalRead'
  have sourceTerminal :
      (fun row : BHist => hsame row terminal ∧ UnaryHistory row) terminal :=
    And.intro (hsame_refl terminal) terminalUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminal ∧ UnaryHistory row)
        (fun row : BHist => Cont e c row ∧ Cont b w r ∧ Cont r l e)
        (fun row : BHist => hsame row terminal ∧ PkgSig bundle terminal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminal sourceTerminal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport terminalRead (hsame_symm source.left),
          bwr, rle⟩
    ledger_sound := by
      intro row source
      exact And.intro source.left terminalPkg
  }
  exact ⟨sameTerminal, pPkg, terminalPkg, terminalPkg', cert⟩

end BEDC.Derived.RealCompletionSelectorSealUp
