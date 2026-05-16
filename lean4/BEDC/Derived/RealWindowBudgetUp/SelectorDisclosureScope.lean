import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp.SelectorDisclosureScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_selector_disclosure_scope [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow selectorRead disclosureRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont request selector selectorRead →
        Cont selectorRead disclosure disclosureRead →
          Cont handoff realSeal sealRead →
            PkgSig bundle disclosureRead pkg →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector
                      disclosure transport route provenance nameRow bundle pkg ∧
                      (hsame row selectorRead ∨ hsame row disclosureRead ∨
                        hsame row sealRead))
                  (fun row : BHist =>
                    Cont request selector selectorRead ∧
                      Cont selectorRead disclosure disclosureRead ∧
                        Cont handoff realSeal sealRead ∧
                          (hsame row selectorRead ∨ hsame row disclosureRead ∨
                            hsame row sealRead))
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier requestSelector selectorDisclosure handoffSeal _disclosurePkg _sealPkg
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed carrier.request_unary carrier.selector_unary requestSelector
  have disclosureReadUnary : UnaryHistory disclosureRead :=
    unary_cont_closed selectorReadUnary carrier.disclosure_unary selectorDisclosure
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed carrier.handoff_unary carrier.realSeal_unary handoffSeal
  have sourceSelector :
      (fun row : BHist =>
        RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
          transport route provenance nameRow bundle pkg ∧
          (hsame row selectorRead ∨ hsame row disclosureRead ∨ hsame row sealRead))
        selectorRead := by
    exact And.intro carrier (Or.inl (hsame_refl selectorRead))
  exact {
    core := {
      carrier_inhabited := Exists.intro selectorRead sourceSelector
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        refine And.intro source.left ?_
        cases source.right with
        | inl sameSelector =>
            exact Or.inl (hsame_trans (hsame_symm same) sameSelector)
        | inr rest =>
            cases rest with
            | inl sameDisclosure =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameDisclosure))
            | inr sameSeal =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm same) sameSeal))
    }
    pattern_sound := by
      intro row source
      exact And.intro requestSelector
        (And.intro selectorDisclosure (And.intro handoffSeal source.right))
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source.right with
        | inl sameSelector =>
            exact unary_transport selectorReadUnary (hsame_symm sameSelector)
        | inr rest =>
            cases rest with
            | inl sameDisclosure =>
                exact unary_transport disclosureReadUnary (hsame_symm sameDisclosure)
            | inr sameSeal =>
                exact unary_transport sealReadUnary (hsame_symm sameSeal)
      exact And.intro rowUnary carrier.provenance_pkg
  }

end BEDC.Derived.RealWindowBudgetUp.SelectorDisclosureScope
