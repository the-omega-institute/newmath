import BEDC.Derived.RegularCauchyCompletionCriterionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyCompletionCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyCompletionCriterionCarrier [AskSetup] [PackageSetup]
    (R W D M L Q H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory M ∧
    UnaryHistory L ∧ UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem RegularCauchyCompletionCriterionRealSealHandoff [AskSetup] [PackageSetup]
    {R W D M L Q H C P N windowRead toleranceRead modulusRead limitRead
      completionRead functorRead recursorRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionCriterionCarrier R W D M L Q H C P N bundle pkg →
      Cont W D windowRead →
        Cont windowRead R toleranceRead →
          Cont toleranceRead M modulusRead →
            Cont modulusRead L limitRead →
              Cont limitRead Q completionRead →
                Cont completionRead H functorRead →
                  Cont functorRead C recursorRead →
                    Cont recursorRead P realRead →
                      PkgSig bundle realRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R ∨ hsame row W ∨ hsame row D ∨
                                hsame row M ∨ hsame row L ∨ hsame row Q ∨
                                  hsame row H ∨ hsame row C ∨ hsame row P ∨
                                    hsame row N ∨ hsame row realRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont W D windowRead ∧
                                Cont windowRead R toleranceRead ∧
                                  Cont toleranceRead M modulusRead ∧
                                    Cont modulusRead L limitRead ∧
                                      Cont limitRead Q completionRead ∧
                                        Cont completionRead H functorRead ∧
                                          Cont functorRead C recursorRead ∧
                                            Cont recursorRead P realRead ∧
                                              PkgSig bundle realRead pkg)
                            hsame ∧
                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: RegularCauchyCompletionCriterionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute toleranceRoute modulusRoute limitRoute completionRoute
    functorRoute recursorRoute realRoute realPkg
  obtain ⟨rUnary, wUnary, dUnary, mUnary, lUnary, qUnary, hUnary, cUnary, pUnary,
    _nUnary, _pkgP, _pkgN⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary rUnary toleranceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary mUnary modulusRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed modulusUnary lUnary limitRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed limitUnary qUnary completionRoute
  have functorUnary : UnaryHistory functorRead :=
    unary_cont_closed completionUnary hUnary functorRoute
  have recursorUnary : UnaryHistory recursorRead :=
    unary_cont_closed functorUnary cUnary recursorRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed recursorUnary pUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨ hsame row L ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧ Cont windowRead R toleranceRead ∧
              Cont toleranceRead M modulusRead ∧ Cont modulusRead L limitRead ∧
                Cont limitRead Q completionRead ∧ Cont completionRead H functorRead ∧
                  Cont functorRead C recursorRead ∧ Cont recursorRead P realRead ∧
                    PkgSig bundle realRead pkg)
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, modulusRoute, limitRoute,
          completionRoute, functorRoute, recursorRoute, realRoute, realPkg⟩
  }
  exact ⟨cert, realUnary⟩

theorem RegularCauchyCompletionCriterionLedgerRefusal [AskSetup] [PackageSetup]
    {R W D M L Q H C P N refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionCriterionCarrier R W D M L Q H C P N bundle pkg →
      Cont Q N refusalRead →
        PkgSig bundle refusalRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨
                  hsame row L ∨ hsame row Q ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row refusalRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont Q N refusalRead ∧ PkgSig bundle refusalRead pkg)
              hsame ∧
            UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: RegularCauchyCompletionCriterionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier refusalRoute refusalPkg
  obtain ⟨_rUnary, _wUnary, _dUnary, _mUnary, _lUnary, qUnary, _hUnary, _cUnary,
    _pUnary, nUnary, _pkgP, _pkgN⟩ := carrier
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed qUnary nUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row M ∨ hsame row L ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q N refusalRead ∧ PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refusalRoute, refusalPkg⟩
  }
  exact ⟨cert, refusalUnary⟩

end BEDC.Derived.RegularCauchyCompletionCriterionUp
