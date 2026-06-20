import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimatePublicTailExport [AskSetup] [PackageSetup]
    {M W D R E H C P N thresholdRead toleranceRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg ->
      Cont M W thresholdRead ->
        Cont thresholdRead D toleranceRead ->
          Cont toleranceRead R sealRead ->
            Cont sealRead C publicRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                          hsame row E ∨ hsame row sealRead ∨ hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M W thresholdRead ∧
                          Cont thresholdRead D toleranceRead ∧
                            Cont toleranceRead R sealRead ∧ Cont sealRead C publicRead ∧
                              PkgSig bundle P pkg)
                      hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeThreshold routeTolerance routeSeal routePublic provenancePkg publicPkg
  obtain ⟨unaryM, unaryW, unaryD, unaryR, _unaryE, _unaryH, unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryW routeThreshold
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary unaryD routeTolerance
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryR routeSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary unaryC routePublic
  have sourcePublic :
      (fun row : BHist =>
        hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary, publicPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row sealRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W thresholdRead ∧
              Cont thresholdRead D toleranceRead ∧ Cont toleranceRead R sealRead ∧
                Cont sealRead C publicRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right.left, routeThreshold, routeTolerance, routeSeal, routePublic,
          provenancePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
