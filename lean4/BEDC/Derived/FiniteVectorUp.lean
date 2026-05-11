import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteVectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteVectorPacket [AskSetup] [PackageSetup]
    (length spine pairs component ledger provenance hidden endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory spine ∧ UnaryHistory pairs ∧
    UnaryHistory component ∧ UnaryHistory ledger ∧ UnaryHistory provenance ∧
      UnaryHistory hidden ∧ UnaryHistory endpoint ∧ Cont length spine endpoint ∧
        PkgSig bundle endpoint pkg

theorem FiniteVectorPacket_length_index_transport [AskSetup] [PackageSetup]
    {length spine pairs component ledger provenance hidden endpoint length' spine' pairs'
      component' ledger' provenance' hidden' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteVectorPacket length spine pairs component ledger provenance hidden endpoint bundle pkg ->
      hsame length length' ->
        hsame spine spine' ->
          hsame pairs pairs' ->
            hsame component component' ->
              hsame ledger ledger' ->
                hsame provenance provenance' ->
                  hsame hidden hidden' ->
                    Cont length' spine' endpoint' ->
                      PkgSig bundle endpoint' pkg ->
                        FiniteVectorPacket length' spine' pairs' component' ledger'
                            provenance' hidden' endpoint' bundle pkg ∧
                          hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro packet sameLength sameSpine samePairs sameComponent sameLedger sameProvenance
    sameHidden endpointCont' endpointPkg'
  obtain ⟨lengthUnary, spineUnary, pairsUnary, componentUnary, ledgerUnary,
    provenanceUnary, hiddenUnary, _endpointUnary, endpointCont, _endpointPkg⟩ := packet
  have lengthUnary' : UnaryHistory length' :=
    unary_transport lengthUnary sameLength
  have spineUnary' : UnaryHistory spine' :=
    unary_transport spineUnary sameSpine
  have pairsUnary' : UnaryHistory pairs' :=
    unary_transport pairsUnary samePairs
  have componentUnary' : UnaryHistory component' :=
    unary_transport componentUnary sameComponent
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport ledgerUnary sameLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have hiddenUnary' : UnaryHistory hidden' :=
    unary_transport hiddenUnary sameHidden
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed lengthUnary' spineUnary' endpointCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLength sameSpine endpointCont endpointCont'
  exact And.intro
    (And.intro lengthUnary'
      (And.intro spineUnary'
        (And.intro pairsUnary'
          (And.intro componentUnary'
            (And.intro ledgerUnary'
              (And.intro provenanceUnary'
                (And.intro hiddenUnary'
                  (And.intro endpointUnary'
                    (And.intro endpointCont' endpointPkg')))))))))
    sameEndpoint

end BEDC.Derived.FiniteVectorUp
