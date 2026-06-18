import BEDC.Derived.RegularCauchyCriterionUp

namespace BEDC.Derived.RegularCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyCriterion_streamname_regseqrat_scope [AskSetup] [PackageSetup]
    {S R M D Q V A H C P N streamRead toleranceRead criterionRead convergenceRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCriterionCarrier S R M D Q V A H C P N bundle pkg ->
      Cont S R streamRead ->
        Cont M D toleranceRead ->
          Cont toleranceRead Q criterionRead ->
            Cont criterionRead V convergenceRead ->
              Cont convergenceRead A realRead ->
                PkgSig bundle realRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
                          hsame row Q ∨ hsame row V ∨ hsame row A ∨
                            hsame row streamRead ∨ hsame row toleranceRead ∨
                              hsame row criterionRead ∨ hsame row convergenceRead ∨
                                hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S R streamRead ∧
                          Cont M D toleranceRead ∧ Cont toleranceRead Q criterionRead ∧
                            Cont criterionRead V convergenceRead ∧
                              Cont convergenceRead A realRead ∧
                                PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory streamRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory criterionRead ∧ UnaryHistory convergenceRead ∧
                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier streamRoute toleranceRoute criterionRoute convergenceRoute realRoute realPkg
  obtain ⟨sUnary, rUnary, mUnary, dUnary, qUnary, vUnary, aUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _streamReadbackModulus, _modulusToleranceCriterion, _namePkg⟩ :=
    carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary rUnary streamRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed mUnary dUnary toleranceRoute
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed toleranceUnary qUnary criterionRoute
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed criterionUnary vUnary convergenceRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed convergenceUnary aUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row M ∨ hsame row D ∨
              hsame row Q ∨ hsame row V ∨ hsame row A ∨ hsame row streamRead ∨
                hsame row toleranceRead ∨ hsame row criterionRead ∨
                  hsame row convergenceRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R streamRead ∧ Cont M D toleranceRead ∧
              Cont toleranceRead Q criterionRead ∧ Cont criterionRead V convergenceRead ∧
                Cont convergenceRead A realRead ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, streamRoute, toleranceRoute, criterionRoute, convergenceRoute,
          realRoute, realPkg⟩
  }
  exact ⟨cert, streamUnary, toleranceUnary, criterionUnary, convergenceUnary, realUnary⟩

end BEDC.Derived.RegularCauchyCriterionUp
