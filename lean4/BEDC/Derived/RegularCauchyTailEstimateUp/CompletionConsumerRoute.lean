import BEDC.Derived.RegularCauchyTailEstimateUp.PublicInterface

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateCompletionConsumerRoute [AskSetup] [PackageSetup]
    {M W D R E _H _C P N thresholdRead toleranceRead readbackRead sealRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory N ->
                Cont M W thresholdRead ->
                  Cont thresholdRead D toleranceRead ->
                    Cont toleranceRead R readbackRead ->
                      Cont readbackRead E sealRead ->
                        Cont sealRead N completionRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                                    hsame row E ∨ hsame row completionRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont M W thresholdRead ∧
                                    Cont thresholdRead D toleranceRead ∧
                                      Cont toleranceRead R readbackRead ∧
                                        Cont readbackRead E sealRead ∧
                                          Cont sealRead N completionRead ∧
                                            PkgSig bundle P pkg)
                                hsame ∧
                              UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                                UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryM unaryW unaryD unaryR unaryE unaryN thresholdRoute toleranceRoute readbackRoute
    sealRoute completionRoute packageRead
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryW thresholdRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryR readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryE sealRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealUnary unaryN completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W thresholdRead ∧ Cont thresholdRead D toleranceRead ∧
              Cont toleranceRead R readbackRead ∧ Cont readbackRead E sealRead ∧
                Cont sealRead N completionRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact
        ⟨source.right, thresholdRoute, toleranceRoute, readbackRoute, sealRoute,
          completionRoute, packageRead⟩
  }
  exact ⟨cert, thresholdUnary, toleranceUnary, readbackUnary, sealUnary, completionUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
