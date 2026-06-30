import BEDC.Derived.CauchyModulusUp

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusCarrier_refinement_consumer_boundary [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule consumption provenance window refinementMeet
      selectorBudget regularSchedule refinementRead dyadicTolerance realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusCarrier precision threshold tolerance schedule consumption provenance window
        bundle pkg →
      UnaryHistory refinementMeet →
        UnaryHistory selectorBudget →
          UnaryHistory regularSchedule →
            Cont window refinementMeet refinementRead →
              Cont refinementRead selectorBudget dyadicTolerance →
                Cont dyadicTolerance regularSchedule realSeal →
                  PkgSig bundle realSeal pkg →
                    SemanticNameCert
                      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row precision ∨ hsame row threshold ∨
                          hsame row tolerance ∨ hsame row schedule ∨
                            hsame row consumption ∨ hsame row provenance ∨
                              hsame row window ∨ hsame row refinementMeet ∨
                                hsame row selectorBudget ∨ hsame row dyadicTolerance ∨
                                  hsame row regularSchedule ∨ hsame row realSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont precision threshold consumption ∧
                          Cont tolerance schedule provenance ∧
                            Cont consumption provenance window ∧
                              Cont window refinementMeet refinementRead ∧
                                Cont refinementRead selectorBudget dyadicTolerance ∧
                                  Cont dyadicTolerance regularSchedule realSeal ∧
                                    PkgSig bundle realSeal pkg)
                      hsame := by
  -- BEDC touchpoint anchor: CauchyModulusCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier refinementUnary selectorUnary regularUnary refinementRoute dyadicRoute
    sealRoute sealPkg
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed carrier.right.right.right.right.right.right.left refinementUnary
      refinementRoute
  have dyadicUnary : UnaryHistory dyadicTolerance :=
    unary_cont_closed refinementReadUnary selectorUnary dyadicRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary regularUnary sealRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
        ⟨source.right, carrier.right.right.right.right.right.right.right.left,
          carrier.right.right.right.right.right.right.right.right.left,
          carrier.right.right.right.right.right.right.right.right.right.left,
          refinementRoute, dyadicRoute, sealRoute, sealPkg⟩
  }

end BEDC.Derived.CauchyModulusUp
