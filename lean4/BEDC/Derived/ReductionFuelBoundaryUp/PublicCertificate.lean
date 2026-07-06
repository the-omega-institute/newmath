import BEDC.Derived.ReductionFuelBoundaryUp.ScopedTimeoutRoute
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

theorem ReductionFuelBoundaryPublicCertificate [AskSetup] [PackageSetup]
    {H F T E U A X C P N endpointRead timeoutRead auditRead replayRead timeoutExport
      endpointExport hostExport publicCertificate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H →
      UnaryHistory F →
        UnaryHistory T →
          UnaryHistory E →
            UnaryHistory U →
              UnaryHistory A →
                UnaryHistory X →
                  UnaryHistory C →
                    UnaryHistory N →
                      Cont H F T →
                        Cont T E endpointRead →
                          Cont T U timeoutRead →
                            Cont endpointRead A auditRead →
                              Cont timeoutRead A replayRead →
                                Cont timeoutRead C timeoutExport →
                                  Cont endpointRead C endpointExport →
                                    Cont auditRead C hostExport →
                                      Cont hostExport N publicCertificate →
                                        PkgSig bundle P pkg →
                                          PkgSig bundle N pkg →
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row publicCertificate ∧
                                                    UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row H ∨ hsame row F ∨
                                                    hsame row T ∨ hsame row E ∨
                                                      hsame row U ∨ hsame row A ∨
                                                        hsame row C ∨
                                                          hsame row hostExport ∨
                                                            hsame row publicCertificate)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧ Cont H F T ∧
                                                    Cont T E endpointRead ∧
                                                      Cont T U timeoutRead ∧
                                                        Cont endpointRead A auditRead ∧
                                                          Cont timeoutRead A replayRead ∧
                                                            Cont auditRead C hostExport ∧
                                                              Cont hostExport N
                                                                publicCertificate ∧
                                                                PkgSig bundle P pkg ∧
                                                                  PkgSig bundle N pkg)
                                                hsame ∧
                                              UnaryHistory publicCertificate := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro _hUnary _fUnary tUnary eUnary uUnary aUnary _xUnary cUnary nUnary hostFuelRoute
    endpointRoute timeoutRoute auditRoute replayRoute _timeoutExportRoute _endpointExportRoute
    hostExportRoute publicRoute provenancePkg namePkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed tUnary eUnary endpointRoute
  have timeoutUnary : UnaryHistory timeoutRead :=
    unary_cont_closed tUnary uUnary timeoutRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed endpointUnary aUnary auditRoute
  have _replayUnary : UnaryHistory replayRead :=
    unary_cont_closed timeoutUnary aUnary replayRoute
  have hostExportUnary : UnaryHistory hostExport :=
    unary_cont_closed auditUnary cUnary hostExportRoute
  have publicUnary : UnaryHistory publicCertificate :=
    unary_cont_closed hostExportUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicCertificate ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row T ∨ hsame row E ∨ hsame row U ∨
              hsame row A ∨ hsame row C ∨ hsame row hostExport ∨
                hsame row publicCertificate)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F T ∧ Cont T E endpointRead ∧
              Cont T U timeoutRead ∧ Cont endpointRead A auditRead ∧
                Cont timeoutRead A replayRead ∧ Cont auditRead C hostExport ∧
                  Cont hostExport N publicCertificate ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicCertificate ⟨hsame_refl publicCertificate, publicUnary⟩
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
        Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, hostFuelRoute, endpointRoute, timeoutRoute, auditRoute,
          replayRoute, hostExportRoute, publicRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.ReductionFuelBoundaryUp
