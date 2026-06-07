import BEDC.Derived.CalculusUp.RootRealSealNonescape

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusContinuousLimitCarrierBudget [AskSetup] [PackageSetup]
    {E R _D L _J _H C P N graphRead limitRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory L →
        UnaryHistory R →
          UnaryHistory E →
            UnaryHistory N →
              Cont C L graphRead →
                Cont graphRead R limitRead →
                  Cont limitRead E sealRead →
                    Cont sealRead N namedRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row C ∨ hsame row L ∨ hsame row R ∨ hsame row E ∨
                                  hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont C L graphRead ∧
                                  Cont graphRead R limitRead ∧ Cont limitRead E sealRead ∧
                                    Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory graphRead ∧ UnaryHistory limitRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryC unaryL unaryR unaryE unaryN graphRoute limitRoute sealRoute namedRoute
    provenancePkg namedPkg
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed unaryC unaryL graphRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed graphUnary unaryR limitRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed limitUnary unaryE sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row L ∨ hsame row R ∨ hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C L graphRead ∧ Cont graphRead R limitRead ∧
              Cont limitRead E sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, graphRoute, limitRoute, sealRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, graphUnary, limitUnary, sealUnary, namedUnary⟩

end BEDC.Derived.CalculusUp
