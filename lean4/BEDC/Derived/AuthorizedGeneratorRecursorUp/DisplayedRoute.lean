import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorDisplayedRoute_ledger_exhaustion
    [AskSetup] [PackageSetup]
    {authorization generator fuel route provenance name branchRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory authorization →
      UnaryHistory generator →
        UnaryHistory fuel →
          UnaryHistory route →
            UnaryHistory name →
              Cont authorization generator branchRead →
                Cont branchRead fuel ledgerRead →
                  PkgSig bundle provenance pkg →
                    UnaryHistory branchRead ∧ UnaryHistory ledgerRead ∧
                      Cont authorization generator branchRead ∧
                        Cont branchRead fuel ledgerRead ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row name ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row name ∧ Cont authorization generator branchRead ∧
                                Cont branchRead fuel ledgerRead)
                            (fun row : BHist => hsame row name ∧ PkgSig bundle provenance pkg)
                            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont SemanticNameCert hsame
  intro authorizationUnary generatorUnary fuelUnary _routeUnary nameUnary
    authorizationGeneratorBranch branchFuelLedger provenancePkg
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed authorizationUnary generatorUnary authorizationGeneratorBranch
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed branchReadUnary fuelUnary branchFuelLedger
  have sourceName : (fun row : BHist => hsame row name ∧ UnaryHistory row) name := by
    exact ⟨hsame_refl name, nameUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row name ∧ Cont authorization generator branchRead ∧
            Cont branchRead fuel ledgerRead)
        (fun row : BHist => hsame row name ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro name sourceName
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
      exact ⟨source.left, authorizationGeneratorBranch, branchFuelLedger⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨branchReadUnary, ledgerReadUnary, authorizationGeneratorBranch, branchFuelLedger, cert⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
