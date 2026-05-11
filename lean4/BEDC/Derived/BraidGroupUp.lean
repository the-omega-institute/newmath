import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BraidGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BraidGroupArtinPacket [AskSetup] [PackageSetup]
    (strand word ledger witness provenance : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  UnaryHistory strand ∧ UnaryHistory word ∧ UnaryHistory provenance ∧
    Cont strand word ledger ∧ Cont ledger provenance witness ∧ PkgSig bundle witness pkg

theorem BraidGroupArtinPacket_ledger_stability [AskSetup] [PackageSetup]
    {strand word ledger witness provenance strand' word' ledger' witness' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupArtinPacket strand word ledger witness provenance bundle pkg ->
      hsame strand strand' ->
        hsame word word' ->
          hsame provenance provenance' ->
            Cont strand' word' ledger' ->
              Cont ledger' provenance' witness' ->
                PkgSig bundle witness' pkg ->
                  BraidGroupArtinPacket strand' word' ledger' witness' provenance'
                      bundle pkg ∧
                    hsame ledger ledger' ∧ hsame witness witness' := by
  intro packet sameStrand sameWord sameProvenance ledgerCont' witnessCont' witnessPkg'
  have strandUnary' : UnaryHistory strand' :=
    unary_transport packet.left sameStrand
  have wordUnary' : UnaryHistory word' :=
    unary_transport packet.right.left sameWord
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.left sameProvenance
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameStrand sameWord packet.right.right.right.left ledgerCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed strandUnary' wordUnary' ledgerCont'
  have sameWitness : hsame witness witness' :=
    cont_respects_hsame sameLedger sameProvenance packet.right.right.right.right.left
      witnessCont'
  have witnessUnary' : UnaryHistory witness' :=
    unary_cont_closed ledgerUnary' provenanceUnary' witnessCont'
  exact
    And.intro
      (And.intro strandUnary'
        (And.intro wordUnary'
          (And.intro provenanceUnary'
            (And.intro ledgerCont' (And.intro witnessCont' witnessPkg')))))
      (And.intro sameLedger sameWitness)

end BEDC.Derived.BraidGroupUp
