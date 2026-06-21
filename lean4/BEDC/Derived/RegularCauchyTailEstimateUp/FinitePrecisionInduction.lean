import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateCarrier_finite_precision_induction [AskSetup] [PackageSetup]
    {M W D R E H C P N extension refinedWindow toleranceRead sealRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg →
      UnaryHistory extension →
        Cont W extension refinedWindow →
          Cont refinedWindow D toleranceRead →
            Cont toleranceRead R sealRead →
              Cont sealRead E finalRead →
                PkgSig bundle P pkg →
                  PkgSig bundle N pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                            hsame row E ∨ hsame row refinedWindow ∨ hsame row finalRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont W extension refinedWindow ∧
                            Cont refinedWindow D toleranceRead ∧
                              Cont toleranceRead R sealRead ∧ Cont sealRead E finalRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory refinedWindow ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier extensionUnary routeRefined routeTolerance routeSeal routeFinal provenancePkg
    namePkg
  obtain ⟨_unaryM, unaryW, unaryD, unaryR, unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed unaryW extensionUnary routeRefined
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed refinedUnary unaryD routeTolerance
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryR routeSeal
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed sealUnary unaryE routeFinal
  have sourceFinal :
      (fun row : BHist => hsame row finalRead ∧ UnaryHistory row) finalRead := by
    exact ⟨hsame_refl finalRead, finalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row refinedWindow ∨ hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W extension refinedWindow ∧
              Cont refinedWindow D toleranceRead ∧ Cont toleranceRead R sealRead ∧
                Cont sealRead E finalRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead sourceFinal
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
      exact
        ⟨source.right, routeRefined, routeTolerance, routeSeal, routeFinal, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, refinedUnary, toleranceUnary, sealUnary, finalUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
