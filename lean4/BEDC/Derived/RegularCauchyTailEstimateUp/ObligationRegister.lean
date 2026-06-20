import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateCarrier_obligation_register [AskSetup] [PackageSetup]
    {M W D R E H C P N thresholdRead toleranceRead sealRead basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg ->
      Cont M W thresholdRead ->
        Cont thresholdRead D toleranceRead ->
          Cont toleranceRead R sealRead ->
            Cont sealRead C basisRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row basisRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M W thresholdRead ∧
                          Cont thresholdRead D toleranceRead ∧
                            Cont toleranceRead R sealRead ∧ Cont sealRead C basisRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory basisRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier thresholdRoute toleranceRoute sealRoute basisRoute provenancePkg namePkg
  obtain ⟨unaryM, unaryW, unaryD, unaryR, _unaryE, _unaryH, unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryW thresholdRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary unaryD toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryR sealRoute
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed sealUnary unaryC basisRoute
  have sourceBasis :
      (fun row : BHist => hsame row basisRead ∧ UnaryHistory row) basisRead := by
    exact ⟨hsame_refl basisRead, basisUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row basisRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W thresholdRead ∧
              Cont thresholdRead D toleranceRead ∧ Cont toleranceRead R sealRead ∧
                Cont sealRead C basisRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro basisRead sourceBasis
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
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, thresholdRoute, toleranceRoute, sealRoute, basisRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, basisUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
