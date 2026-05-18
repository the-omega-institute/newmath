import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_zero_facing_source_accountability
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' provenance' sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      Cont basic eta' analytic' ->
        Cont analytic' functional transports' ->
          Cont transports' routes provenance' ->
            PkgSig bundle provenance' pkg ->
              hsame eta eta' ->
                UnaryHistory routes ->
                  UnaryHistory name ->
                    Cont routes name sourceRead ->
                      PkgSig bundle sourceRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨
                                hsame row functional ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                                  hsame row sourceRead)
                            (fun row : BHist =>
                              PkgSig bundle provenance' pkg ∧
                                PkgSig bundle sourceRead pkg ∧ hsame row sourceRead)
                            hsame ∧
                          UnaryHistory sourceRead ∧ hsame sourceRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame append
  intro packet basicRoute functionalRoute provenanceRoute provenancePkg etaSame routesUnary
    nameUnary sourceRoute sourcePkg
  obtain ⟨_analyticSame, _transportsSame, _provenanceSame, namePkg, _provenancePkg'⟩ :=
    ZetaContinuationWitnessPacket_dependency_ledger
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (eta' := eta') (analytic' := analytic')
      (transports' := transports') (provenance' := provenance')
      (bundle := bundle) (pkg := pkg) packet basicRoute functionalRoute provenanceRoute
      provenancePkg etaSame
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed routesUnary nameUnary sourceRoute
  have sourceSame : hsame sourceRead (append routes name) :=
    sourceRoute
  have sourceCarrier :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨
              hsame row functional ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                hsame row sourceRead)
          (fun row : BHist =>
            PkgSig bundle provenance' pkg ∧ PkgSig bundle sourceRead pkg ∧
              hsame row sourceRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro sourceRead sourceCarrier
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, sourcePkg, source.left⟩
    }
  exact ⟨cert, sourceUnary, sourceSame⟩

end BEDC.Derived.ZetaContinuationWitnessUp
