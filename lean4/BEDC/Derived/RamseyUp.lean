import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RamseyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RamseyColouringCarrier_obligation_surface [AskSetup] [PackageSetup]
    {vertexSpine subsetSpine colorEndpoint lookupLedger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vertexSpine ->
      UnaryHistory subsetSpine ->
        UnaryHistory colorEndpoint ->
          Cont vertexSpine subsetSpine lookupLedger ->
            Cont lookupLedger colorEndpoint provenance ->
              Cont provenance colorEndpoint endpoint ->
                PkgSig bundle endpoint pkg ->
                  UnaryHistory lookupLedger ∧ UnaryHistory provenance ∧
                    UnaryHistory endpoint ∧ hsame lookupLedger (append vertexSpine subsetSpine) ∧
                      hsame provenance (append lookupLedger colorEndpoint) ∧
                        hsame endpoint (append provenance colorEndpoint) ∧
                          PkgSig bundle endpoint pkg := by
  intro vertexUnary subsetUnary colorUnary lookupRow provenanceRow endpointRow pkgSig
  have lookupUnary : UnaryHistory lookupLedger :=
    unary_cont_closed vertexUnary subsetUnary lookupRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed lookupUnary colorUnary provenanceRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary colorUnary endpointRow
  exact
    ⟨lookupUnary,
      provenanceUnary,
      endpointUnary,
      lookupRow,
      provenanceRow,
      endpointRow,
      pkgSig⟩

end BEDC.Derived.RamseyUp
