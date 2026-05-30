import BEDC.Derived.FareySequenceUp.TasteGate

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_denominator_refinement_induction [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N levelRead mediantRead toleranceRead
      bracketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A levelRead ->
        Cont levelRead M mediantRead ->
          Cont mediantRead L toleranceRead ->
            Cont toleranceRead T bracketRead ->
              PkgSig bundle bracketRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row bracketRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                        hsame row T ∨ hsame row levelRead ∨ hsame row mediantRead ∨
                          hsame row toleranceRead ∨ hsame row bracketRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont B A levelRead ∧
                        Cont levelRead M mediantRead ∧
                          Cont mediantRead L toleranceRead ∧
                            Cont toleranceRead T bracketRead ∧
                              PkgSig bundle bracketRead pkg)
                    hsame ∧
                  UnaryHistory levelRead ∧ UnaryHistory mediantRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory bracketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier levelRoute mediantRoute toleranceRoute bracketRoute bracketPkg
  obtain ⟨boundaryUnary, adjacencyUnary, mediantUnary, levelUnary, toleranceUnary,
    _sternUnary, _denominatorUnary, _quotientUnary, _windowUnary, _regularUnary,
    _gapUnary, _endpointUnary, _handoffUnary, _classifierUnary, _packageUnary,
    _nameUnary, _adjacencyEmpty, _sternEmpty, _mediantEmpty, _gapEmpty, _endpointEmpty,
    _packagePkg⟩ := carrier
  have levelReadUnary : UnaryHistory levelRead :=
    unary_cont_closed boundaryUnary adjacencyUnary levelRoute
  have mediantReadUnary : UnaryHistory mediantRead :=
    unary_cont_closed levelReadUnary mediantUnary mediantRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed mediantReadUnary levelUnary toleranceRoute
  have bracketReadUnary : UnaryHistory bracketRead :=
    unary_cont_closed toleranceReadUnary toleranceUnary bracketRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bracketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row levelRead ∨ hsame row mediantRead ∨ hsame row toleranceRead ∨
                hsame row bracketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B A levelRead ∧ Cont levelRead M mediantRead ∧
              Cont mediantRead L toleranceRead ∧ Cont toleranceRead T bracketRead ∧
                PkgSig bundle bracketRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bracketRead ⟨hsame_refl bracketRead, bracketReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, levelRoute, mediantRoute, toleranceRoute, bracketRoute,
          bracketPkg⟩
  }
  exact ⟨cert, levelReadUnary, mediantReadUnary, toleranceReadUnary, bracketReadUnary⟩

end BEDC.Derived.FareySequenceUp
