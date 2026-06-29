import BEDC.Derived.SubmartingaleUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubmartingaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubmartingaleCarrier_upcrossing_ledger_exactness [AskSetup] [PackageSetup]
    {endpoint comparison stopWindow lower upper crossing doobLedger replay provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory endpoint →
      UnaryHistory comparison →
        UnaryHistory lower →
          UnaryHistory upper →
            UnaryHistory replay →
              Cont endpoint comparison stopWindow →
                Cont lower upper crossing →
                  Cont stopWindow crossing doobLedger →
                    Cont doobLedger replay localName →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row doobLedger ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row endpoint ∨ hsame row comparison ∨
                                  hsame row stopWindow ∨ hsame row crossing ∨
                                    hsame row doobLedger ∨ hsame row replay ∨
                                      hsame row localName)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont endpoint comparison stopWindow ∧
                                  Cont lower upper crossing ∧
                                    Cont stopWindow crossing doobLedger ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory stopWindow ∧ UnaryHistory crossing ∧
                              UnaryHistory doobLedger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro endpointUnary comparisonUnary lowerUnary upperUnary _replayUnary stopRoute crossingRoute
    doobRoute _localRoute provenancePkg localNamePkg
  have stopWindowUnary : UnaryHistory stopWindow :=
    unary_cont_closed endpointUnary comparisonUnary stopRoute
  have crossingUnary : UnaryHistory crossing :=
    unary_cont_closed lowerUnary upperUnary crossingRoute
  have doobLedgerUnary : UnaryHistory doobLedger :=
    unary_cont_closed stopWindowUnary crossingUnary doobRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row doobLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row comparison ∨ hsame row stopWindow ∨
              hsame row crossing ∨ hsame row doobLedger ∨ hsame row replay ∨
                hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpoint comparison stopWindow ∧
              Cont lower upper crossing ∧ Cont stopWindow crossing doobLedger ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro doobLedger ⟨hsame_refl doobLedger, doobLedgerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, stopRoute, crossingRoute, doobRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, stopWindowUnary, crossingUnary, doobLedgerUnary⟩

end BEDC.Derived.SubmartingaleUp
