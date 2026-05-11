import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ApartnessRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApartnessRealCarrier [AskSetup] [PackageSetup]
    (left right radius window leftReadback rightReadback ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧ UnaryHistory window ∧
    UnaryHistory leftReadback ∧ UnaryHistory rightReadback ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont left window leftReadback ∧
        Cont right window rightReadback ∧ Cont left right endpoint ∧
          Cont leftReadback rightReadback ledger ∧ PkgSig bundle endpoint pkg

theorem ApartnessRealCarrier_symmetry_stability [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback ledger swappedLedger provenance endpoint
      swappedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealCarrier left right radius window leftReadback rightReadback ledger provenance
        endpoint bundle pkg ->
      Cont right left swappedEndpoint -> Cont rightReadback leftReadback swappedLedger ->
        PkgSig bundle swappedEndpoint pkg ->
          ApartnessRealCarrier right left radius window rightReadback leftReadback swappedLedger
              provenance swappedEndpoint bundle pkg ∧
            hsame radius radius ∧ Cont rightReadback leftReadback swappedLedger := by
  intro carrier swappedEndpointRow swappedLedgerRow swappedPkg
  have swappedEndpointUnary : UnaryHistory swappedEndpoint :=
    unary_cont_closed carrier.right.left carrier.left swappedEndpointRow
  have swappedLedgerUnary : UnaryHistory swappedLedger :=
    unary_cont_closed carrier.right.right.right.right.right.left
      carrier.right.right.right.right.left swappedLedgerRow
  constructor
  · constructor
    · exact carrier.right.left
    · constructor
      · exact carrier.left
      · constructor
        · exact carrier.right.right.left
        · constructor
          · exact carrier.right.right.right.left
          · constructor
            · exact carrier.right.right.right.right.right.left
            · constructor
              · exact carrier.right.right.right.right.left
              · constructor
                · exact swappedLedgerUnary
                · constructor
                  · exact carrier.right.right.right.right.right.right.right.left
                  · constructor
                    · exact swappedEndpointUnary
                    · constructor
                      · exact carrier.right.right.right.right.right.right.right.right.right.right.left
                      · constructor
                        · exact carrier.right.right.right.right.right.right.right.right.right.left
                        · constructor
                          · exact swappedEndpointRow
                          · constructor
                            · exact swappedLedgerRow
                            · exact swappedPkg
  · constructor
    · exact hsame_refl radius
    · exact swappedLedgerRow

end BEDC.Derived.ApartnessRealUp
