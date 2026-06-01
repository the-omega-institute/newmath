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
    {I S W D R Q H C P N scheduleRead windowRead toleranceRead readbackRead sealRead
      structuralRead namedRead filterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusSpaceCarrier I S W D R Q H C P N ->
      Cont I S scheduleRead ->
        Cont scheduleRead W windowRead ->
          Cont windowRead D toleranceRead ->
            Cont toleranceRead R readbackRead ->
              Cont readbackRead Q sealRead ->
                Cont H C structuralRead ->
                  Cont P N namedRead ->
                    Cont sealRead structuralRead filterRead ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle N pkg ->
                          PkgSig bundle filterRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row filterRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row I ∨ hsame row S ∨ hsame row W ∨ hsame row D ∨
                                    hsame row R ∨ hsame row Q ∨ hsame row sealRead ∨
                                      hsame row structuralRead ∨ hsame row filterRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle N pkg ∧ PkgSig bundle filterRead pkg)
                                hsame ∧
                              UnaryHistory filterRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier scheduleRoute windowRoute toleranceRoute readbackRoute sealRoute
    structuralRoute namingRoute filterRoute provenancePkg namePkg filterPkg
  obtain ⟨tailCert, _scheduleUnary, _windowUnary, _toleranceUnary, _readbackUnary,
    sealUnary, structuralUnary, _namedUnary⟩ :=
      CauchyModulusSpaceTailComposition (bundle := bundle) (pkg := pkg) carrier
        scheduleRoute windowRoute toleranceRoute readbackRoute sealRoute structuralRoute
        namingRoute provenancePkg namePkg
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed sealUnary structuralUnary filterRoute
  have sourceFilter :
      (fun row : BHist => hsame row filterRead ∧ UnaryHistory row) filterRead := by
    exact ⟨hsame_refl filterRead, filterUnary⟩
  constructor
  · exact {
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg, filterPkg⟩
    }
  · exact filterUnary

end BEDC.Derived.CauchyUp
