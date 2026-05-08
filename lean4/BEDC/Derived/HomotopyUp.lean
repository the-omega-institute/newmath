import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HomotopyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HomotopyBHistSourcePacket [AskSetup] [PackageSetup]
    (source target deformation interval provenance endpointRead ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory deformation ∧
    UnaryHistory interval ∧ UnaryHistory provenance ∧ Cont deformation interval endpointRead ∧
      Cont endpointRead provenance ledger ∧ Cont ledger target endpoint ∧
        PkgSig bundle endpoint pkg

theorem HomotopyBHistSourcePacket_interval_parameter_transport [AskSetup] [PackageSetup]
    {source target deformation interval intervalPrime provenance endpointRead endpointReadPrime
      ledger endpoint endpointPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HomotopyBHistSourcePacket source target deformation interval provenance endpointRead ledger
        endpoint bundle pkg ->
      hsame interval intervalPrime ->
        Cont deformation intervalPrime endpointReadPrime ->
          Cont endpointReadPrime provenance ledger ->
            Cont ledger target endpointPrime ->
              PkgSig bundle endpointPrime pkg ->
                HomotopyBHistSourcePacket source target deformation intervalPrime provenance
                    endpointReadPrime ledger endpointPrime bundle pkg ∧
                  hsame endpointRead endpointReadPrime ∧ hsame endpoint endpointPrime := by
  intro packet sameInterval endpointReadCont' ledgerCont' endpointCont' pkgSig'
  have intervalUnary' : UnaryHistory intervalPrime :=
    unary_transport packet.right.right.right.left sameInterval
  have endpointReadUnary' : UnaryHistory endpointReadPrime :=
    unary_cont_closed packet.right.right.left intervalUnary' endpointReadCont'
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpointReadUnary' packet.right.right.right.right.left ledgerCont'
  have endpointUnary' : UnaryHistory endpointPrime :=
    unary_cont_closed ledgerUnary packet.right.left endpointCont'
  have sameEndpointRead : hsame endpointRead endpointReadPrime :=
    cont_respects_hsame (hsame_refl deformation) sameInterval
      packet.right.right.right.right.right.left endpointReadCont'
  have sameEndpoint : hsame endpoint endpointPrime :=
    cont_respects_hsame (hsame_refl ledger) (hsame_refl target)
      packet.right.right.right.right.right.right.right.left endpointCont'
  exact And.intro
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro intervalUnary'
            (And.intro packet.right.right.right.right.left
              (And.intro endpointReadCont'
                (And.intro ledgerCont'
                  (And.intro endpointCont' pkgSig'))))))))
    (And.intro sameEndpointRead sameEndpoint)

theorem HomotopyBHistSourcePacket_deformation_composition_row [AskSetup] [PackageSetup]
    {source middle target deformation deformation' interval provenance endpointRead ledger endpoint
      endpointRead' ledger' endpoint' composedDeformation composedRead composedLedger
      composedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HomotopyBHistSourcePacket source middle deformation interval provenance endpointRead ledger
        endpoint bundle pkg ->
      HomotopyBHistSourcePacket middle target deformation' interval provenance endpointRead' ledger'
        endpoint' bundle pkg ->
        Cont deformation deformation' composedDeformation ->
          Cont composedDeformation interval composedRead ->
            Cont composedRead provenance composedLedger ->
              Cont composedLedger target composedEndpoint ->
                PkgSig bundle composedEndpoint pkg ->
                  HomotopyBHistSourcePacket source target composedDeformation interval provenance
                    composedRead composedLedger composedEndpoint bundle pkg := by
  intro leftPacket rightPacket deformationCont composedReadCont composedLedgerCont
    composedEndpointCont composedPkg
  have composedDeformationUnary : UnaryHistory composedDeformation :=
    unary_cont_closed leftPacket.right.right.left rightPacket.right.right.left deformationCont
  have composedReadUnary : UnaryHistory composedRead :=
    unary_cont_closed composedDeformationUnary leftPacket.right.right.right.left composedReadCont
  have composedLedgerUnary : UnaryHistory composedLedger :=
    unary_cont_closed composedReadUnary leftPacket.right.right.right.right.left composedLedgerCont
  have composedEndpointUnary : UnaryHistory composedEndpoint :=
    unary_cont_closed composedLedgerUnary rightPacket.right.left composedEndpointCont
  exact
    And.intro leftPacket.left
      (And.intro rightPacket.right.left
        (And.intro composedDeformationUnary
          (And.intro leftPacket.right.right.right.left
          (And.intro leftPacket.right.right.right.right.left
            (And.intro composedReadCont
              (And.intro composedLedgerCont
                (And.intro composedEndpointCont composedPkg)))))))

theorem HomotopyBHistSourcePacket_interval_endpoint_determinacy [AskSetup] [PackageSetup]
    {source target deformation interval interval' provenance endpointRead endpointRead' ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HomotopyBHistSourcePacket source target deformation interval provenance endpointRead ledger
        endpoint bundle pkg ->
      HomotopyBHistSourcePacket source target deformation interval' provenance endpointRead' ledger
        endpoint bundle pkg ->
        hsame endpointRead endpointRead' -> hsame interval interval' := by
  intro leftPacket rightPacket sameEndpointRead
  have rightEndpointReadCont : Cont deformation interval' endpointRead :=
    cont_result_hsame_transport rightPacket.right.right.right.right.right.left
      (hsame_symm sameEndpointRead)
  exact cont_left_cancel leftPacket.right.right.right.right.right.left rightEndpointReadCont

theorem HomotopyBHistSourcePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {source target deformation interval provenance endpointRead ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HomotopyBHistSourcePacket source target deformation interval provenance endpointRead ledger
        endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists source target deformation interval provenance endpointRead ledger : BHist,
              HomotopyBHistSourcePacket source target deformation interval provenance
                endpointRead ledger row bundle pkg)
          (fun row : BHist =>
            exists source target deformation interval provenance endpointRead ledger : BHist,
              HomotopyBHistSourcePacket source target deformation interval provenance
                endpointRead ledger row bundle pkg)
          (fun row : BHist =>
            exists source target deformation interval provenance endpointRead ledger : BHist,
              HomotopyBHistSourcePacket source target deformation interval provenance
                endpointRead ledger row bundle pkg)
          (fun left right : BHist =>
            (exists source target deformation interval provenance endpointRead ledger : BHist,
              HomotopyBHistSourcePacket source target deformation interval provenance
                endpointRead ledger left bundle pkg) ∧
              (exists source target deformation interval provenance endpointRead ledger : BHist,
                HomotopyBHistSourcePacket source target deformation interval provenance
                  endpointRead ledger right bundle pkg) ∧
                hsame left right) ∧
        Cont endpointRead provenance ledger ∧ PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          refine Exists.intro endpoint ?_
          refine Exists.intro source ?_
          refine Exists.intro target ?_
          refine Exists.intro deformation ?_
          refine Exists.intro interval ?_
          refine Exists.intro provenance ?_
          refine Exists.intro endpointRead ?_
          exact Exists.intro ledger packet
        equiv_refl := by
          intro endpoint source
          exact And.intro source (And.intro source (hsame_refl endpoint))
        equiv_symm := by
          intro left right classified
          exact And.intro classified.right.left
            (And.intro classified.left (hsame_symm classified.right.right))
        equiv_trans := by
          intro left middle right classifiedLM classifiedMR
          exact And.intro classifiedLM.left
            (And.intro classifiedMR.right.left
              (hsame_trans classifiedLM.right.right classifiedMR.right.right))
        carrier_respects_equiv := by
          intro left right classified _source
          exact classified.right.left
      }
      pattern_sound := by
        intro endpoint source
        exact source
      ledger_sound := by
        intro endpoint source
        exact source
    }
  · exact And.intro packet.right.right.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right

end BEDC.Derived.HomotopyUp
