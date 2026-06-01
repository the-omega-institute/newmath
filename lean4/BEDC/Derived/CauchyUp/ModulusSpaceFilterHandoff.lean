import BEDC.Derived.CauchyUp.ModulusSpaceTail

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusSpaceFilterHandoff [AskSetup] [PackageSetup]
    {I S W D R Q H C P N scheduleRead toleranceRead readbackRead sealRead structuralRead
      filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusSpaceCarrier I S W D R Q H C P N ->
      Cont I S scheduleRead ->
        Cont scheduleRead D toleranceRead ->
          Cont toleranceRead R readbackRead ->
            Cont readbackRead Q sealRead ->
              Cont H C structuralRead ->
                Cont sealRead structuralRead filterRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row filterRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row I ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
                              hsame row R ∨ hsame row Q ∨ hsame row filterRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory filterRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier scheduleRoute toleranceRoute readbackRoute sealRoute structuralRoute
    filterRoute provenancePkg namePkg
  obtain ⟨iUnary, sUnary, _wUnary, dUnary, rUnary, qUnary, hUnary, cUnary, _pUnary,
    _nUnary⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed iUnary sUnary scheduleRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed scheduleReadUnary dUnary toleranceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary rUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary qUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have filterReadUnary : UnaryHistory filterRead :=
    unary_cont_closed sealReadUnary structuralReadUnary filterRoute
  have sourceFilter :
      (fun row : BHist => hsame row filterRead ∧ UnaryHistory row) filterRead := by
    exact ⟨hsame_refl filterRead, filterReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row filterRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
              hsame row R ∨ hsame row Q ∨ hsame row filterRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro filterRead sourceFilter
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, filterReadUnary⟩

end BEDC.Derived.CauchyUp
