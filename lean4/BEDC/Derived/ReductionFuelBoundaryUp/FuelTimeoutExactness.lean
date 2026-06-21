import BEDC.Derived.ReductionFuelBoundaryUp.EndpointTimeoutDisjointness

namespace BEDC.Derived.ReductionFuelBoundaryUp.FuelTimeoutExactness

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReductionFuelBoundary_fuel_timeout_exactness [AskSetup] [PackageSetup]
    {H F T U A X C P N timeoutRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H ->
      UnaryHistory F ->
        UnaryHistory T ->
          UnaryHistory U ->
            UnaryHistory A ->
              UnaryHistory X ->
                UnaryHistory C ->
                  Cont H F T ->
                    Cont T U timeoutRead ->
                      Cont timeoutRead A auditRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row timeoutRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row F ∨ hsame row T ∨ hsame row U ∨
                                    hsame row timeoutRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont H F T ∧
                                    Cont T U timeoutRead ∧
                                      Cont timeoutRead A auditRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧ UnaryHistory timeoutRead ∧
                              UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro hUnary fUnary tUnary uUnary aUnary _xUnary _cUnary hostFuelRoute timeoutRoute
    auditRoute provenancePkg namePkg
  have timeoutUnary : UnaryHistory timeoutRead :=
    unary_cont_closed tUnary uUnary timeoutRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed timeoutUnary aUnary auditRoute
  have sourceTimeout :
      (fun row : BHist => hsame row timeoutRead ∧ UnaryHistory row) timeoutRead := by
    exact ⟨hsame_refl timeoutRead, timeoutUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row timeoutRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row T ∨ hsame row U ∨ hsame row timeoutRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F T ∧ Cont T U timeoutRead ∧
              Cont timeoutRead A auditRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro timeoutRead sourceTimeout
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
        intro _row _other sameRows sourceRow
        constructor
        · exact hsame_trans (hsame_symm sameRows) sourceRow.left
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, hostFuelRoute, timeoutRoute, auditRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, timeoutUnary, auditUnary⟩

end BEDC.Derived.ReductionFuelBoundaryUp.FuelTimeoutExactness
