import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateRegSeqRatHandoff [AskSetup] [PackageSetup]
    {M W D R E H C P N dyadicRead regSeqRead sealRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg →
      Cont D W dyadicRead →
        Cont dyadicRead R regSeqRead →
          Cont regSeqRead E sealRead →
            Cont sealRead H handoffRead →
              PkgSig bundle P pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                          hsame row H ∨ hsame row P ∨ hsame row N ∨
                            hsame row handoffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont D W dyadicRead ∧
                          Cont dyadicRead R regSeqRead ∧ Cont regSeqRead E sealRead ∧
                            Cont sealRead H handoffRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory regSeqRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier dyadicRoute regSeqRoute sealRoute handoffRoute provenancePkg namePkg
  obtain ⟨_unaryM, unaryW, unaryD, unaryR, unaryE, unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed unaryD unaryW dyadicRoute
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed dyadicUnary unaryR regSeqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regSeqUnary unaryE sealRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sealUnary unaryH handoffRoute
  have sourceHandoff :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row P ∨ hsame row N ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W dyadicRead ∧
              Cont dyadicRead R regSeqRead ∧ Cont regSeqRead E sealRead ∧
                Cont sealRead H handoffRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoff
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, dyadicRoute, regSeqRoute, sealRoute, handoffRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, dyadicUnary, regSeqUnary, sealUnary, handoffUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
