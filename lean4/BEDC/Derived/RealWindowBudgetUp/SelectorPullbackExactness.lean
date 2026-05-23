import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_selector_pullback_exactness [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance nameRow
      selectorRead disclosureRead sealRead pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure transport route
        provenance nameRow bundle pkg ->
      Cont selector disclosure selectorRead ->
        Cont selectorRead route disclosureRead ->
          Cont handoff realSeal sealRead ->
            Cont disclosureRead sealRead pullbackRead ->
              PkgSig bundle pullbackRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                          disclosure transport route provenance nameRow bundle pkg ∧
                        (hsame row selectorRead ∨ hsame row disclosureRead ∨
                          hsame row sealRead ∨ hsame row pullbackRead))
                    (fun row : BHist =>
                      Cont selector disclosure selectorRead ∧
                        Cont selectorRead route disclosureRead ∧
                          Cont handoff realSeal sealRead ∧
                            Cont disclosureRead sealRead pullbackRead ∧
                              (hsame row selectorRead ∨ hsame row disclosureRead ∨
                                hsame row sealRead ∨ hsame row pullbackRead))
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle pullbackRead pkg)
                    hsame ∧ UnaryHistory pullbackRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier selectorDisclosure selectorReadRoute handoffRealSeal disclosureSeal pullbackPkg
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed carrier.selector_unary carrier.disclosure_unary selectorDisclosure
  have disclosureReadUnary : UnaryHistory disclosureRead :=
    unary_cont_closed selectorReadUnary carrier.route_unary selectorReadRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffRealSeal
  have pullbackReadUnary : UnaryHistory pullbackRead :=
    unary_cont_closed disclosureReadUnary sealReadUnary disclosureSeal
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro pullbackRead
            ⟨carrier, Or.inr (Or.inr (Or.inr (hsame_refl pullbackRead)))⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          refine ⟨source.left, ?_⟩
          cases source.right with
          | inl rowSelector =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) rowSelector)
          | inr tail =>
              cases tail with
              | inl rowDisclosure =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowDisclosure))
              | inr tail' =>
                  cases tail' with
                  | inl rowSeal =>
                      exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowSeal)))
                  | inr rowPullback =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowPullback)))
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨selectorDisclosure, selectorReadRoute, handoffRealSeal, disclosureSeal,
            source.right⟩
      ledger_sound := by
        intro _row source
        cases source.right with
        | inl rowSelector =>
            exact
              ⟨unary_transport selectorReadUnary (hsame_symm rowSelector), pullbackPkg⟩
        | inr tail =>
            cases tail with
            | inl rowDisclosure =>
                exact
                  ⟨unary_transport disclosureReadUnary (hsame_symm rowDisclosure),
                    pullbackPkg⟩
            | inr tail' =>
                cases tail' with
                | inl rowSeal =>
                    exact ⟨unary_transport sealReadUnary (hsame_symm rowSeal), pullbackPkg⟩
                | inr rowPullback =>
                    exact
                      ⟨unary_transport pullbackReadUnary (hsame_symm rowPullback),
                        pullbackPkg⟩
    }
  · exact pullbackReadUnary

end BEDC.Derived.RealWindowBudgetUp
