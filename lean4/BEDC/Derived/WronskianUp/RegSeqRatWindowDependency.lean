import BEDC.Derived.WronskianUp.Carrier

namespace BEDC.Derived.WronskianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WronskianCarrier_regseqrat_window_dependency [AskSetup] [PackageSetup]
    {F D J Omega S R E H C P N derivativeRead determinantRead regseqRead toleranceRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    WronskianCarrier F D J Omega S R E H C P N bundle pkg →
      Cont F D derivativeRead →
        Cont derivativeRead J determinantRead →
          Cont S R regseqRead →
            Cont regseqRead P toleranceRead →
              Cont toleranceRead E sealRead →
                Cont sealRead H namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
                            hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                              hsame row C ∨ hsame row P ∨ hsame row N ∨
                                hsame row derivativeRead ∨ hsame row determinantRead ∨
                                  hsame row regseqRead ∨ hsame row toleranceRead ∨
                                    hsame row sealRead ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont F D derivativeRead ∧
                            Cont derivativeRead J determinantRead ∧ Cont S R regseqRead ∧
                              Cont regseqRead P toleranceRead ∧ Cont toleranceRead E sealRead ∧
                                Cont sealRead H namedRead ∧ PkgSig bundle namedRead pkg)
                        hsame ∧
                      UnaryHistory derivativeRead ∧ UnaryHistory determinantRead ∧
                        UnaryHistory regseqRead ∧ UnaryHistory toleranceRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier derivativeRoute determinantRoute regseqRoute toleranceRoute sealRoute namedRoute
    namedPkg
  obtain ⟨fUnary, dUnary, jUnary, _omegaUnary, sUnary, rUnary, eUnary, hUnary,
    _cUnary, pUnary, _nUnary, _familyRoute, _determinantCarrierRoute,
    _valueCarrierRoute, _scopeRoute, _provenancePkg, _namePkg⟩ := carrier
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed fUnary dUnary derivativeRoute
  have determinantUnary : UnaryHistory determinantRead :=
    unary_cont_closed derivativeUnary jUnary determinantRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed sUnary rUnary regseqRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed regseqUnary pUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary hUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row D ∨ hsame row J ∨ hsame row Omega ∨
              hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row derivativeRead ∨
                  hsame row determinantRead ∨ hsame row regseqRead ∨
                    hsame row toleranceRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F D derivativeRead ∧
              Cont derivativeRead J determinantRead ∧ Cont S R regseqRead ∧
                Cont regseqRead P toleranceRead ∧ Cont toleranceRead E sealRead ∧
                  Cont sealRead H namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨namedRead, hsame_refl namedRead, namedUnary⟩
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
      exact
        ⟨source.right, derivativeRoute, determinantRoute, regseqRoute, toleranceRoute,
          sealRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, derivativeUnary, determinantUnary, regseqUnary, toleranceUnary, sealUnary,
      namedUnary⟩

end BEDC.Derived.WronskianUp
