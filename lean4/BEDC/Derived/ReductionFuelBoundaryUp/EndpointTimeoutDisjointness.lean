import BEDC.Derived.ReductionFuelBoundaryUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReductionFuelBoundaryUp.EndpointTimeoutDisjointness

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReductionFuelBoundary_endpoint_timeout_disjointness [AskSetup] [PackageSetup]
    {H F T E U A X C P N endpointRead timeoutRead auditRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H →
      UnaryHistory F →
        UnaryHistory T →
          UnaryHistory E →
            UnaryHistory U →
              UnaryHistory A →
                UnaryHistory X →
                  UnaryHistory C →
                    Cont H F T →
                      Cont T E endpointRead →
                        Cont T U timeoutRead →
                          Cont endpointRead A auditRead →
                            Cont timeoutRead A replayRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row endpointRead ∨ hsame row timeoutRead) ∧
                                          UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row H ∨ hsame row F ∨ hsame row T ∨
                                          hsame row E ∨ hsame row U ∨ hsame row A ∨
                                            hsame row endpointRead ∨ hsame row timeoutRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont H F T ∧
                                          Cont T E endpointRead ∧ Cont T U timeoutRead ∧
                                            Cont endpointRead A auditRead ∧
                                              Cont timeoutRead A replayRead ∧
                                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory endpointRead ∧ UnaryHistory timeoutRead ∧
                                      UnaryHistory auditRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig SemanticNameCert UnaryHistory
  intro hUnary fUnary tUnary eUnary uUnary aUnary _xUnary _cUnary hostFuelRoute
    endpointRoute timeoutRoute auditRoute replayRoute provenancePkg namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed tUnary eUnary endpointRoute
  have timeoutUnary : UnaryHistory timeoutRead :=
    unary_cont_closed tUnary uUnary timeoutRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed endpointUnary aUnary auditRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed timeoutUnary aUnary replayRoute
  have sourceEndpoint :
      (fun row : BHist =>
        (hsame row endpointRead ∨ hsame row timeoutRead) ∧ UnaryHistory row)
        endpointRead :=
    ⟨Or.inl (hsame_refl endpointRead), endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row endpointRead ∨ hsame row timeoutRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row T ∨ hsame row E ∨ hsame row U ∨
              hsame row A ∨ hsame row endpointRead ∨ hsame row timeoutRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F T ∧ Cont T E endpointRead ∧
              Cont T U timeoutRead ∧ Cont endpointRead A auditRead ∧
                Cont timeoutRead A replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead sourceEndpoint
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
        constructor
        · cases source.left with
          | inl sameEndpoint =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)
          | inr sameTimeout =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameTimeout)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEndpoint =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inl sameEndpoint))))))
      | inr sameTimeout =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr sameTimeout))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, hostFuelRoute, endpointRoute, timeoutRoute, auditRoute, replayRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, endpointUnary, timeoutUnary, auditUnary, replayUnary⟩

end BEDC.Derived.ReductionFuelBoundaryUp.EndpointTimeoutDisjointness
