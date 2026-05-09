import BEDC.Derived.DirichletUnitUp
import BEDC.Derived.NumFieldUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.DirichletUnitUp
open BEDC.Derived.NumFieldUp

inductive RegulatorLedgerSpine : List BHist -> BHist -> Prop where
  | nil {endpoint : BHist} : UnaryHistory endpoint -> RegulatorLedgerSpine [] endpoint
  | cons {row tail endpoint : BHist} {rest : List BHist} :
      UnaryHistory row -> RegulatorLedgerSpine rest tail -> Cont row tail endpoint ->
        RegulatorLedgerSpine (row :: rest) endpoint

theorem RegulatorLedgerSpine_rows_unary
    {rows : List BHist} {endpoint row : BHist} :
    RegulatorLedgerSpine rows endpoint -> List.Mem row rows -> UnaryHistory row := by
  intro spine rowMem
  induction spine with
  | nil _ =>
      cases rowMem
  | cons rowUnary _ _ ih =>
      cases rowMem with
      | head =>
          exact rowUnary
      | tail _ restMem =>
          exact ih restMem

def RegulatorRootInputPacket [AskSetup] [PackageSetup]
    (duSource unit inverse law unitLedger lawLedger duProvenance nfSource rank layout provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  DirichletUnitHistoryCarrier duSource unit inverse law unitLedger lawLedger duProvenance ∧
    NumFieldRatReflexiveCarrier nfSource ∧ UnaryHistory rank ∧ UnaryHistory layout ∧
      Cont rank layout provenance ∧ Cont provenance duProvenance endpoint ∧
        PkgSig bundle endpoint pkg

theorem RegulatorRootInputPacket_dirichletunit_input_boundary [AskSetup] [PackageSetup]
    {duSource unit inverse law unitLedger lawLedger duProvenance nfSource rank layout provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatorRootInputPacket duSource unit inverse law unitLedger lawLedger duProvenance
      nfSource rank layout provenance endpoint bundle pkg ->
      DirichletUnitHistoryCarrier duSource unit inverse law unitLedger lawLedger duProvenance ∧
        NumFieldRatReflexiveCarrier nfSource ∧ UnaryHistory rank ∧ UnaryHistory layout ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont rank layout provenance ∧
            Cont provenance duProvenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have duReadback :=
    DirichletUnitHistoryCarrier_readback_obligation
      (source := duSource) (unit := unit) (inverse := inverse) (law := law)
      (unitLedger := unitLedger) (lawLedger := lawLedger) (provenance := duProvenance)
      packet.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary duReadback.right.right.left
      packet.right.right.right.right.right.left
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro provenanceUnary
            (And.intro endpointUnary
              (And.intro packet.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.left
                  packet.right.right.right.right.right.right)))))))

def RegulatorRootLedgerPacket [AskSetup] [PackageSetup]
    (dirichlet numfield unit inverse rank basis determinant provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dirichlet ∧ UnaryHistory numfield ∧ UnaryHistory unit ∧
    UnaryHistory inverse ∧ UnaryHistory rank ∧ UnaryHistory basis ∧
      UnaryHistory determinant ∧ UnaryHistory provenance ∧
        Cont provenance determinant endpoint ∧ PkgSig bundle endpoint pkg

theorem RegulatorRootInputPacket_ledger_exactness [AskSetup] [PackageSetup]
    {dirichlet numfield unit inverse rank basis determinant provenance endpoint
      determinantLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatorRootLedgerPacket dirichlet numfield unit inverse rank basis determinant provenance
        endpoint bundle pkg ->
      Cont basis determinant determinantLedger ->
        UnaryHistory determinantLedger ∧ hsame determinantLedger (append basis determinant) ∧
          hsame endpoint (append provenance determinant) ∧ PkgSig bundle endpoint pkg := by
  intro packet determinantLedgerCont
  cases packet with
  | intro _ rest =>
      cases rest with
      | intro _ rest =>
          cases rest with
          | intro _ rest =>
              cases rest with
              | intro _ rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro basisUnary rest =>
                          cases rest with
                          | intro determinantUnary rest =>
                              cases rest with
                              | intro provenanceUnary rest =>
                                  cases rest with
                                  | intro endpointCont endpointPkg =>
                                      have determinantLedgerUnary :
                                          UnaryHistory determinantLedger :=
                                        unary_cont_closed basisUnary determinantUnary
                                        determinantLedgerCont
                                      exact And.intro determinantLedgerUnary
                                        (And.intro determinantLedgerCont
                                          (And.intro endpointCont endpointPkg))

theorem RegulatorRootInputPacket_root_namecert_threshold [AskSetup] [PackageSetup]
    {duSource unit inverse law unitLedger lawLedger duProvenance nfSource rank layout provenance
      endpoint threshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatorRootInputPacket duSource unit inverse law unitLedger lawLedger duProvenance
        nfSource rank layout provenance endpoint bundle pkg ->
      Cont endpoint provenance threshold ->
      PkgSig bundle threshold pkg ->
          UnaryHistory threshold ∧ hsame threshold (append endpoint provenance) ∧
            RegulatorRootInputPacket duSource unit inverse law unitLedger lawLedger duProvenance
              nfSource rank layout provenance endpoint bundle pkg := by
  intro packet thresholdCont _
  have boundary :=
    RegulatorRootInputPacket_dirichletunit_input_boundary
      (duSource := duSource) (unit := unit) (inverse := inverse) (law := law)
      (unitLedger := unitLedger) (lawLedger := lawLedger) (duProvenance := duProvenance)
      (nfSource := nfSource) (rank := rank) (layout := layout) (provenance := provenance)
      (endpoint := endpoint) (bundle := bundle) (pkg := pkg) packet
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed boundary.right.right.right.right.right.left
      boundary.right.right.right.right.left thresholdCont
  exact And.intro thresholdUnary (And.intro thresholdCont packet)

end BEDC.Derived.RegulatorUp
