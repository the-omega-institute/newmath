import BEDC.Derived.ReductionFuelBoundaryUp.EndpointTimeoutDisjointness

namespace BEDC.Derived.ReductionFuelBoundaryUp.TotalHostNonescape

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReductionFuelBoundaryTotalHostNonescape [AskSetup] [PackageSetup]
    {H F T E U A X C P N endpointRead timeoutRead auditRead replayRead hostExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H ->
      UnaryHistory F ->
        UnaryHistory T ->
          UnaryHistory E ->
            UnaryHistory U ->
              UnaryHistory A ->
                UnaryHistory X ->
                  UnaryHistory C ->
                    Cont H F T ->
                      Cont T E endpointRead ->
                        Cont T U timeoutRead ->
                          Cont endpointRead A auditRead ->
                            Cont timeoutRead A replayRead ->
                              Cont auditRead C hostExport ->
                                PkgSig bundle P pkg ->
                                  PkgSig bundle N pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row hostExport ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row H ∨ hsame row F ∨ hsame row T ∨
                                            hsame row E ∨ hsame row U ∨ hsame row A ∨
                                              hsame row C ∨ hsame row hostExport)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont H F T ∧
                                            Cont T E endpointRead ∧ Cont T U timeoutRead ∧
                                              Cont endpointRead A auditRead ∧
                                                Cont timeoutRead A replayRead ∧
                                                  Cont auditRead C hostExport ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory endpointRead ∧ UnaryHistory timeoutRead ∧
                                        UnaryHistory auditRead ∧ UnaryHistory replayRead ∧
                                          UnaryHistory hostExport := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro hUnary fUnary tUnary eUnary uUnary aUnary _xUnary cUnary hostFuelRoute
    endpointRoute timeoutRoute auditRoute replayRoute hostExportRoute provenancePkg namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed tUnary eUnary endpointRoute
  have timeoutUnary : UnaryHistory timeoutRead :=
    unary_cont_closed tUnary uUnary timeoutRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed endpointUnary aUnary auditRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed timeoutUnary aUnary replayRoute
  have hostExportUnary : UnaryHistory hostExport :=
    unary_cont_closed auditUnary cUnary hostExportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hostExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row T ∨ hsame row E ∨ hsame row U ∨
              hsame row A ∨ hsame row C ∨ hsame row hostExport)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F T ∧ Cont T E endpointRead ∧
              Cont T U timeoutRead ∧ Cont endpointRead A auditRead ∧
                Cont timeoutRead A replayRead ∧ Cont auditRead C hostExport ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro hostExport ⟨hsame_refl hostExport, hostExportUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, hostFuelRoute, endpointRoute, timeoutRoute, auditRoute, replayRoute,
          hostExportRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, endpointUnary, timeoutUnary, auditUnary, replayUnary, hostExportUnary⟩

end BEDC.Derived.ReductionFuelBoundaryUp.TotalHostNonescape
