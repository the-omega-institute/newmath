import BEDC.Derived.CanonicalTailChoiceUp.Nonescape

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_cofinality_stability [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N indexRead tailRead laterTail replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont M E indexRead →
        Cont indexRead T tailRead →
          hsame laterTail tailRead →
            Cont laterTail H replayRead →
              PkgSig bundle replayRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
                        hsame row S ∨ hsame row R ∨ hsame row H ∨
                          hsame row C0 ∨ hsame row P ∨ hsame row N ∨
                            hsame row indexRead ∨ hsame row tailRead ∨
                              hsame row laterTail ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M E indexRead ∧
                        Cont indexRead T tailRead ∧ Cont laterTail H replayRead ∧
                          PkgSig bundle N pkg ∧ PkgSig bundle replayRead pkg)
                    hsame ∧
                  UnaryHistory indexRead ∧ UnaryHistory tailRead ∧
                    UnaryHistory laterTail ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: CanonicalTailChoiceCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier indexRoute tailRoute sameLaterTail replayRoute replayPkg
  obtain ⟨mUnary, eUnary, _iUnary, tUnary, _sUnary, _rUnary, hUnary, _c0Unary,
    _pUnary, _nUnary, _pPkg, nPkg⟩ := carrier
  have indexUnary : UnaryHistory indexRead :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tUnary tailRoute
  have laterTailUnary : UnaryHistory laterTail :=
    unary_transport tailUnary (hsame_symm sameLaterTail)
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed laterTailUnary hUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
              hsame row S ∨ hsame row R ∨ hsame row H ∨ hsame row C0 ∨
                hsame row P ∨ hsame row N ∨ hsame row indexRead ∨
                  hsame row tailRead ∨ hsame row laterTail ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M E indexRead ∧ Cont indexRead T tailRead ∧
              Cont laterTail H replayRead ∧ PkgSig bundle N pkg ∧
                PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨replayRead, hsame_refl replayRead, replayUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, indexRoute, tailRoute, replayRoute, nPkg, replayPkg⟩
  }
  exact ⟨cert, indexUnary, tailUnary, laterTailUnary, replayUnary⟩

end BEDC.Derived.CanonicalTailChoiceUp
