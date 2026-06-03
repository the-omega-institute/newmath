import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusSpaceDiagonalFamilyExactness [AskSetup] [PackageSetup]
    {I S W D R Q H C P N schedule tolerance readback sealRead diagonalRead structural
      named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusSpaceCarrier I S W D R Q H C P N →
      Cont I S schedule →
        Cont schedule D tolerance →
          Cont tolerance R readback →
            Cont readback Q sealRead →
              Cont sealRead H diagonalRead →
                Cont C P structural →
                  Cont structural N named →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row I ∨ hsame row S ∨ hsame row D ∨ hsame row R ∨
                                hsame row Q ∨ hsame row diagonalRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory schedule ∧ UnaryHistory tolerance ∧
                            UnaryHistory readback ∧ UnaryHistory sealRead ∧
                              UnaryHistory diagonalRead ∧ UnaryHistory structural ∧
                                UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier scheduleRoute toleranceRoute readbackRoute sealRoute diagonalRoute
    structuralRoute namedRoute provenancePkg namePkg
  obtain ⟨iUnary, sUnary, _wUnary, dUnary, rUnary, qUnary, hUnary, cUnary, pUnary,
    nUnary⟩ := carrier
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed iUnary sUnary scheduleRoute
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed scheduleUnary dUnary toleranceRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed toleranceUnary rUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary qUnary sealRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed sealReadUnary hUnary diagonalRoute
  have structuralUnary : UnaryHistory structural :=
    unary_cont_closed cUnary pUnary structuralRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed structuralUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row S ∨ hsame row D ∨ hsame row R ∨
              hsame row Q ∨ hsame row diagonalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro diagonalRead ⟨hsame_refl diagonalRead, diagonalReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, scheduleUnary, toleranceUnary, readbackUnary, sealReadUnary, diagonalReadUnary,
      structuralUnary, namedUnary⟩

end BEDC.Derived.CauchyUp
