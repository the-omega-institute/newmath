import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateCarrier_tail_induction_scope [AskSetup] [PackageSetup]
    {M W D R E H C P N thresholdRead toleranceRead sealRead inductionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg ->
      Cont M W thresholdRead ->
        Cont thresholdRead D toleranceRead ->
          Cont toleranceRead R sealRead ->
            Cont sealRead W inductionRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                          hsame row E ∨ hsame row inductionRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M W thresholdRead ∧
                          Cont thresholdRead D toleranceRead ∧
                            Cont toleranceRead R sealRead ∧ Cont sealRead W inductionRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory thresholdRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory inductionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeThreshold routeTolerance routeSeal routeInduction provenancePkg namePkg
  obtain ⟨unaryM, unaryW, unaryD, unaryR, _unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryW routeThreshold
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary unaryD routeTolerance
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryR routeSeal
  have inductionUnary : UnaryHistory inductionRead :=
    unary_cont_closed sealUnary unaryW routeInduction
  have sourceInduction :
      (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row) inductionRead := by
    exact ⟨hsame_refl inductionRead, inductionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row inductionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W thresholdRead ∧
              Cont thresholdRead D toleranceRead ∧ Cont toleranceRead R sealRead ∧
                Cont sealRead W inductionRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro inductionRead sourceInduction
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
        ⟨source.right, routeThreshold, routeTolerance, routeSeal, routeInduction,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, thresholdUnary, toleranceUnary, sealUnary, inductionUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
