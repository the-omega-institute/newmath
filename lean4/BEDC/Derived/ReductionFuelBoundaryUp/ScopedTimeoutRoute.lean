import BEDC.Derived.ReductionFuelBoundaryUp.ScopedSubstrateRoute
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ReductionFuelBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReductionFuelBoundaryScopedTimeoutRoute [AskSetup] [PackageSetup]
    {H F T E U A X C P N endpointRead timeoutRead auditRead replayRead timeoutExport
      endpointExport : BHist}
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
                              Cont timeoutRead C timeoutExport →
                                Cont endpointRead C endpointExport →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            (hsame row timeoutExport ∨
                                                hsame row endpointExport) ∧
                                              UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row H ∨ hsame row F ∨ hsame row T ∨
                                              hsame row E ∨ hsame row U ∨ hsame row A ∨
                                                hsame row C ∨ hsame row timeoutExport ∨
                                                  hsame row endpointExport)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont H F T ∧
                                              Cont T E endpointRead ∧ Cont T U timeoutRead ∧
                                                Cont endpointRead A auditRead ∧
                                                  Cont timeoutRead A replayRead ∧
                                                    Cont timeoutRead C timeoutExport ∧
                                                      Cont endpointRead C endpointExport ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory timeoutExport ∧
                                          UnaryHistory endpointExport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _hUnary _fUnary tUnary eUnary uUnary aUnary _xUnary cUnary hostFuelRoute
    endpointRoute timeoutRoute auditRoute replayRoute timeoutExportRoute endpointExportRoute
    provenancePkg namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed tUnary eUnary endpointRoute
  have timeoutUnary : UnaryHistory timeoutRead :=
    unary_cont_closed tUnary uUnary timeoutRoute
  have _auditUnary : UnaryHistory auditRead :=
    unary_cont_closed endpointUnary aUnary auditRoute
  have _replayUnary : UnaryHistory replayRead :=
    unary_cont_closed timeoutUnary aUnary replayRoute
  have timeoutExportUnary : UnaryHistory timeoutExport :=
    unary_cont_closed timeoutUnary cUnary timeoutExportRoute
  have endpointExportUnary : UnaryHistory endpointExport :=
    unary_cont_closed endpointUnary cUnary endpointExportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row timeoutExport ∨ hsame row endpointExport) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row T ∨ hsame row E ∨ hsame row U ∨
              hsame row A ∨ hsame row C ∨ hsame row timeoutExport ∨
                hsame row endpointExport)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F T ∧ Cont T E endpointRead ∧
              Cont T U timeoutRead ∧ Cont endpointRead A auditRead ∧
                Cont timeoutRead A replayRead ∧ Cont timeoutRead C timeoutExport ∧
                  Cont endpointRead C endpointExport ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro timeoutExport
          ⟨Or.inl (hsame_refl timeoutExport), timeoutExportUnary⟩
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
          | inl sameTimeout =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameTimeout)
          | inr sameEndpoint =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameEndpoint)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameTimeout =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr <| Or.inl sameTimeout
      | inr sameEndpoint =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inr <| Or.inr sameEndpoint
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, hostFuelRoute, endpointRoute, timeoutRoute, auditRoute,
          replayRoute, timeoutExportRoute, endpointExportRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, timeoutExportUnary, endpointExportUnary⟩

theorem ReductionFuelBoundaryScopedRoute [AskSetup] [PackageSetup]
    {H F T E U A X C P N endpointRead timeoutRead auditRead replayRead timeoutExport
      endpointExport hostExport : BHist}
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
                              Cont timeoutRead C timeoutExport →
                                Cont endpointRead C endpointExport →
                                  Cont auditRead C hostExport →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row hostExport ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row H ∨ hsame row F ∨ hsame row T ∨
                                                hsame row E ∨ hsame row U ∨ hsame row A ∨
                                                  hsame row C ∨ hsame row hostExport)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont H F T ∧
                                                Cont T E endpointRead ∧
                                                  Cont T U timeoutRead ∧
                                                    Cont endpointRead A auditRead ∧
                                                      Cont timeoutRead A replayRead ∧
                                                        Cont auditRead C hostExport ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                            hsame ∧
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                (hsame row timeoutExport ∨
                                                    hsame row endpointExport) ∧
                                                  UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row H ∨ hsame row F ∨ hsame row T ∨
                                                  hsame row E ∨ hsame row U ∨ hsame row A ∨
                                                    hsame row C ∨ hsame row timeoutExport ∨
                                                      hsame row endpointExport)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont H F T ∧
                                                  Cont T E endpointRead ∧
                                                    Cont T U timeoutRead ∧
                                                      Cont endpointRead A auditRead ∧
                                                        Cont timeoutRead A replayRead ∧
                                                          Cont timeoutRead C timeoutExport ∧
                                                            Cont endpointRead C endpointExport ∧
                                                              PkgSig bundle P pkg ∧
                                                                PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory hostExport ∧
                                              UnaryHistory timeoutExport ∧
                                                UnaryHistory endpointExport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro hUnary fUnary tUnary eUnary uUnary aUnary xUnary cUnary hostFuelRoute
    endpointRoute timeoutRoute auditRoute replayRoute timeoutExportRoute endpointExportRoute
    hostExportRoute provenancePkg namePkg
  have hostCert :=
    ReductionFuelBoundaryScopedSubstrateRoute hUnary fUnary tUnary eUnary uUnary aUnary
      xUnary cUnary hostFuelRoute endpointRoute timeoutRoute auditRoute replayRoute
      hostExportRoute provenancePkg namePkg
  have timeoutCert :=
    ReductionFuelBoundaryScopedTimeoutRoute hUnary fUnary tUnary eUnary uUnary aUnary
      xUnary cUnary hostFuelRoute endpointRoute timeoutRoute auditRoute replayRoute
      timeoutExportRoute endpointExportRoute provenancePkg namePkg
  exact
    ⟨hostCert.left, timeoutCert.left, hostCert.right, timeoutCert.right.left,
      timeoutCert.right.right⟩

end BEDC.Derived.ReductionFuelBoundaryUp
