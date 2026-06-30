import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateModulusDominanceCriterion [AskSetup] [PackageSetup]
    {M W D R E H C P N coarseRead toleranceRead sealRead refinedRead nestedRead
      dominanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg →
      Cont M W coarseRead →
        Cont coarseRead D toleranceRead →
          Cont toleranceRead R sealRead →
            Cont sealRead W refinedRead →
              Cont refinedRead E nestedRead →
                Cont M D dominanceRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle nestedRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row dominanceRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                              hsame row E ∨ hsame row nestedRead ∨ hsame row dominanceRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont M W coarseRead ∧
                              Cont coarseRead D toleranceRead ∧
                                Cont toleranceRead R sealRead ∧ Cont sealRead W refinedRead ∧
                                  Cont refinedRead E nestedRead ∧
                                    Cont M D dominanceRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle nestedRead pkg)
                          hsame ∧
                        UnaryHistory dominanceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier routeCoarse routeTolerance routeSeal routeRefined routeNested routeDominance
    provenance nestedPkg
  obtain ⟨unaryM, unaryW, unaryD, unaryR, unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have coarseUnary : UnaryHistory coarseRead :=
    unary_cont_closed unaryM unaryW routeCoarse
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed coarseUnary unaryD routeTolerance
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryR routeSeal
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed sealUnary unaryW routeRefined
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed refinedUnary unaryE routeNested
  have dominanceUnary : UnaryHistory dominanceRead :=
    unary_cont_closed unaryM unaryD routeDominance
  have sourceDominance :
      (fun row : BHist => hsame row dominanceRead ∧ UnaryHistory row) dominanceRead := by
    exact ⟨hsame_refl dominanceRead, dominanceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dominanceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row nestedRead ∨ hsame row dominanceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M W coarseRead ∧ Cont coarseRead D toleranceRead ∧
              Cont toleranceRead R sealRead ∧ Cont sealRead W refinedRead ∧
                Cont refinedRead E nestedRead ∧ Cont M D dominanceRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle nestedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dominanceRead sourceDominance
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
        ⟨source.right, routeCoarse, routeTolerance, routeSeal, routeRefined, routeNested,
          routeDominance, provenance, nestedPkg⟩
  }
  exact ⟨cert, dominanceUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
