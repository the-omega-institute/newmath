import BEDC.Derived.CliffordUp
import BEDC.Derived.GroupUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.CliffordUp
open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpinGroupRootCarrier [AskSetup] [PackageSetup]
    (unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
    GroupSingletonCarrier groupWord ∧ Cont cliffordEndpoint groupWord spinEndpoint ∧
      PkgSig bundle ledger pkg

theorem SpinGroupRootCarrier_source_scope [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
        GroupSingletonCarrier groupWord ∧ UnaryHistory spinEndpoint ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have clifford : CliffordCarrierPackage unit vector product boundary cliffordEndpoint :=
    carrier.left
  have productUnary : UnaryHistory product :=
    unary_cont_closed clifford.right.left clifford.right.left clifford.right.right.right.left
  have endpointUnary : UnaryHistory cliffordEndpoint :=
    unary_cont_closed productUnary clifford.right.right.left clifford.right.right.right.right
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm carrier.right.left)
  have spinUnary : UnaryHistory spinEndpoint :=
    unary_cont_closed endpointUnary groupUnary carrier.right.right.left
  exact
    And.intro clifford
      (And.intro carrier.right.left
        (And.intro spinUnary
          (And.intro carrier.right.right.left carrier.right.right.right)))

theorem SpinGroupRootCarrier_group_law_transport [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint cliffordEndpoint' groupWord groupWord'
      spinEndpoint spinEndpoint' ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame cliffordEndpoint cliffordEndpoint' ->
        hsame groupWord groupWord' ->
          Cont product boundary cliffordEndpoint' ->
            Cont cliffordEndpoint' groupWord' spinEndpoint' ->
              SpinGroupRootCarrier unit vector product boundary cliffordEndpoint' groupWord'
                  spinEndpoint' ledger bundle pkg ∧ hsame spinEndpoint spinEndpoint' := by
  intro carrier sameClifford sameGroup productBoundary spinCont
  have clifford' :
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint' :=
    And.intro carrier.left.left
      (And.intro carrier.left.right.left
        (And.intro carrier.left.right.right.left
          (And.intro carrier.left.right.right.right.left productBoundary)))
  have group' : GroupSingletonCarrier groupWord' :=
    hsame_trans (hsame_symm sameGroup) carrier.right.left
  have sameSpin : hsame spinEndpoint spinEndpoint' :=
    cont_respects_hsame sameClifford sameGroup carrier.right.right.left spinCont
  exact
    And.intro
      (And.intro clifford'
        (And.intro group'
          (And.intro spinCont carrier.right.right.right)))
      sameSpin

theorem SpinGroupRootCarrier_concrete_lift_closure [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unit' vector'
      product' boundary' cliffordEndpoint' groupWord' spinEndpoint' ledger' composedLift
      composedProjection composedLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SpinGroupRootCarrier unit' vector' product' boundary' cliffordEndpoint' groupWord'
          spinEndpoint' ledger' bundle pkg ->
        Cont spinEndpoint spinEndpoint' composedLift ->
          Cont composedLift BHist.Empty composedProjection ->
            PkgSig bundle composedLedger pkg ->
              UnaryHistory composedLift ∧ UnaryHistory composedProjection ∧
                hsame composedLift (append spinEndpoint spinEndpoint') ∧
                  hsame composedProjection composedLift ∧ PkgSig bundle composedLedger pkg := by
  intro carrier carrier' liftRow projectionRow composedPkg
  have scope :=
    SpinGroupRootCarrier_source_scope carrier
  have scope' :=
    SpinGroupRootCarrier_source_scope carrier'
  have liftUnary : UnaryHistory composedLift :=
    unary_cont_closed scope.right.right.left scope'.right.right.left liftRow
  have projectionUnary : UnaryHistory composedProjection :=
    unary_cont_closed liftUnary unary_empty projectionRow
  have projectionSame : hsame composedProjection composedLift :=
    cont_right_unit_result projectionRow
  exact And.intro liftUnary
    (And.intro projectionUnary
      (And.intro liftRow
        (And.intro projectionSame composedPkg)))

theorem SpinGroupRootCarrier_root_namecert_threshold_package [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint) hsame ∧
        UnaryHistory spinEndpoint ∧ Cont cliffordEndpoint groupWord spinEndpoint ∧
          PkgSig bundle ledger pkg := by
  intro carrier
  have sourceScope :
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
        GroupSingletonCarrier groupWord ∧ UnaryHistory spinEndpoint ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg :=
    SpinGroupRootCarrier_source_scope carrier
  have cert :
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint) hsame := by
    refine {
      core := ?core
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound
    }
    · refine {
        carrier_inhabited := ?carrier_inhabited
        equiv_refl := ?equiv_refl
        equiv_symm := ?equiv_symm
        equiv_trans := ?equiv_trans
        carrier_respects_equiv := ?carrier_respects_equiv
      }
      · exact Exists.intro spinEndpoint (hsame_refl spinEndpoint)
      · intro row _source
        exact hsame_refl row
      · intro row other sameRows
        exact hsame_symm sameRows
      · intro row other third sameFirst sameSecond
        exact hsame_trans sameFirst sameSecond
      · intro row other sameRows rowSource
        exact hsame_trans (hsame_symm sameRows) rowSource
    · intro row source
      exact source
    · intro row source
      exact source
  exact
    And.intro cert
      (And.intro sourceScope.right.right.left
        (And.intro sourceScope.right.right.right.left sourceScope.right.right.right.right))

theorem SpinGroupRootCarrier_public_consumer_boundary_coverage [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
        UnaryHistory cliffordEndpoint ∧ GroupSingletonCarrier groupWord ∧
          UnaryHistory spinEndpoint ∧ Cont vector vector product ∧
            Cont product boundary cliffordEndpoint ∧
              Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have cliffordExact :
      UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
        UnaryHistory cliffordEndpoint ∧ Cont vector vector product ∧
          Cont product boundary cliffordEndpoint ∧
            hsame product (append vector vector) ∧
              hsame cliffordEndpoint (append (append vector vector) boundary) :=
    CliffordCarrierPackage_universal_ledger_exactness carrier.left
  have sourceScope :
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
        GroupSingletonCarrier groupWord ∧ UnaryHistory spinEndpoint ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg :=
    SpinGroupRootCarrier_source_scope carrier
  exact
    And.intro cliffordExact.left
      (And.intro cliffordExact.right.left
        (And.intro cliffordExact.right.right.left
          (And.intro cliffordExact.right.right.right.left
            (And.intro cliffordExact.right.right.right.right.left
              (And.intro sourceScope.right.left
                (And.intro sourceScope.right.right.left
                  (And.intro cliffordExact.right.right.right.right.right.left
                    (And.intro cliffordExact.right.right.right.right.right.right.left
                      (And.intro sourceScope.right.right.right.left
                        sourceScope.right.right.right.right)))))))))

theorem SpinGroupRootCarrier_clifford_unit_lift [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CliffordCarrierPackage unit vector product boundary cliffordEndpoint ->
      Cont cliffordEndpoint BHist.Empty spinEndpoint ->
        PkgSig bundle ledger pkg ->
          SpinGroupRootCarrier unit vector product boundary cliffordEndpoint BHist.Empty
            spinEndpoint ledger bundle pkg ∧ hsame spinEndpoint cliffordEndpoint := by
  intro clifford endpointUnit packageSig
  exact And.intro
    (And.intro clifford
      (And.intro (hsame_refl BHist.Empty)
        (And.intro endpointUnit packageSig)))
    (cont_right_unit_result endpointUnit)

theorem SpinGroupRootCarrier_ledger_semantic_exhaustion [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SemanticNameCert (fun h : BHist => hsame h spinEndpoint)
        (fun h : BHist => hsame h spinEndpoint)
        (fun h : BHist => hsame h spinEndpoint) hsame ∧
        UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
          UnaryHistory cliffordEndpoint ∧ UnaryHistory spinEndpoint ∧
            Cont vector vector product ∧ Cont product boundary cliffordEndpoint ∧
              Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have coverage := SpinGroupRootCarrier_public_consumer_boundary_coverage carrier
  have endpointSelf : hsame spinEndpoint spinEndpoint :=
    hsame_refl spinEndpoint
  have cert :
      SemanticNameCert (fun h : BHist => hsame h spinEndpoint)
        (fun h : BHist => hsame h spinEndpoint)
        (fun h : BHist => hsame h spinEndpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro spinEndpoint endpointSelf
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro h carrierH
      exact carrierH
    ledger_sound := by
      intro h carrierH
      exact carrierH
  }
  exact And.intro cert
    (And.intro coverage.left
      (And.intro coverage.right.left
        (And.intro coverage.right.right.left
          (And.intro coverage.right.right.right.left
            (And.intro coverage.right.right.right.right.left
              (And.intro coverage.right.right.right.right.right.right.left
                (And.intro coverage.right.right.right.right.right.right.right.left
                  (And.intro coverage.right.right.right.right.right.right.right.right.left
                    (And.intro
                      coverage.right.right.right.right.right.right.right.right.right.left
                      coverage.right.right.right.right.right.right.right.right.right.right)))))))))

theorem SpinGroupRootCarrier_threshold_obligation_triple [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger thresholdLedger :
      BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont product groupWord thresholdLedger ->
        UnaryHistory unit ∧ UnaryHistory product ∧ UnaryHistory spinEndpoint ∧
          UnaryHistory thresholdLedger ∧ Cont vector vector product ∧
            Cont product boundary cliffordEndpoint ∧ Cont cliffordEndpoint groupWord spinEndpoint ∧
              hsame product (append vector vector) ∧
                hsame spinEndpoint (append cliffordEndpoint groupWord) ∧
                  hsame thresholdLedger (append product groupWord) ∧ PkgSig bundle ledger pkg := by
  intro carrier thresholdCont
  have cliffordExact := CliffordCarrierPackage_universal_ledger_exactness carrier.left
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm sourceScope.right.left)
  have thresholdUnary : UnaryHistory thresholdLedger :=
    unary_cont_closed cliffordExact.right.right.left groupUnary thresholdCont
  exact And.intro cliffordExact.left
    (And.intro cliffordExact.right.right.left
      (And.intro sourceScope.right.right.left
        (And.intro thresholdUnary
          (And.intro cliffordExact.right.right.right.right.right.left
            (And.intro cliffordExact.right.right.right.right.right.right.left
              (And.intro sourceScope.right.right.right.left
                (And.intro cliffordExact.right.right.right.right.right.right.right.left
                  (And.intro sourceScope.right.right.right.left
                    (And.intro thresholdCont sourceScope.right.right.right.right)))))))))

theorem SpinGroupRootCarrier_unit_lift [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unitEndpoint
      unitLedger : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont unit BHist.Empty unitEndpoint ->
        Cont unitEndpoint groupWord unitLedger ->
          SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord
              spinEndpoint ledger bundle pkg ∧
            UnaryHistory unitEndpoint ∧ UnaryHistory unitLedger ∧ hsame unitEndpoint unit ∧
              hsame unitLedger (append unitEndpoint groupWord) := by
  intro carrier unitEndpointCont unitLedgerCont
  have unitEndpointUnary : UnaryHistory unitEndpoint :=
    unary_cont_closed carrier.left.left unary_empty unitEndpointCont
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm carrier.right.left)
  have unitLedgerUnary : UnaryHistory unitLedger :=
    unary_cont_closed unitEndpointUnary groupUnary unitLedgerCont
  exact
    ⟨carrier, unitEndpointUnary, unitLedgerUnary, cont_right_unit_result unitEndpointCont,
      unitLedgerCont⟩

theorem SpinGroupRootCarrier_root_namecert_obligation_surface [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row other : BHist =>
            hsame row other ∧ hsame row spinEndpoint ∧ hsame other spinEndpoint) ∧
        CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
          GroupSingletonCarrier groupWord ∧ Cont cliffordEndpoint groupWord spinEndpoint ∧
            UnaryHistory spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have scope := SpinGroupRootCarrier_source_scope carrier
  have endpointSelf : hsame spinEndpoint spinEndpoint :=
    hsame_refl spinEndpoint
  have cert :
      SemanticNameCert (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row : BHist => hsame row spinEndpoint)
          (fun row other : BHist =>
            hsame row other ∧ hsame row spinEndpoint ∧ hsame other spinEndpoint) := {
    core := {
      carrier_inhabited := Exists.intro spinEndpoint endpointSelf
      equiv_refl := by
        intro row source
        exact And.intro (hsame_refl row) (And.intro source source)
      equiv_symm := by
        intro row other classified
        exact And.intro (hsame_symm classified.left)
          (And.intro classified.right.right classified.right.left)
      equiv_trans := by
        intro row other target classifiedRO classifiedOT
        have sameRT : hsame row target :=
          hsame_trans classifiedRO.left classifiedOT.left
        exact And.intro sameRT
          (And.intro classifiedRO.right.left classifiedOT.right.right)
      carrier_respects_equiv := by
        intro row other classified _source
        exact classified.right.right
    }
    pattern_sound := by
      intro row source
      exact source
    ledger_sound := by
      intro row source
      exact source
  }
  exact And.intro cert
    (And.intro scope.left
      (And.intro scope.right.left
        (And.intro scope.right.right.right.left
          (And.intro scope.right.right.left scope.right.right.right.right))))

theorem SpinGroupRootCarrier_public_consumer_boundary_exhaustion [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame row spinEndpoint ->
        UnaryHistory row ∧ UnaryHistory spinEndpoint ∧ Cont cliffordEndpoint groupWord
          spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier sameRowSpin
  have sourceScope :
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
        GroupSingletonCarrier groupWord ∧ UnaryHistory spinEndpoint ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg :=
    SpinGroupRootCarrier_source_scope carrier
  have rowUnary : UnaryHistory row :=
    unary_transport sourceScope.right.right.left (hsame_symm sameRowSpin)
  exact And.intro rowUnary
    (And.intro sourceScope.right.right.left
      (And.intro sourceScope.right.right.right.left sourceScope.right.right.right.right))

theorem SpinGroupRootCarrier_spin_double_cover_boundary [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger coverEndpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont spinEndpoint BHist.Empty coverEndpoint ->
        UnaryHistory spinEndpoint ∧ UnaryHistory coverEndpoint ∧ hsame coverEndpoint spinEndpoint ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier coverRow
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have coverUnary : UnaryHistory coverEndpoint :=
    unary_cont_closed sourceScope.right.right.left unary_empty coverRow
  have sameCoverSpin : hsame coverEndpoint spinEndpoint :=
    cont_right_unit_result coverRow
  exact And.intro sourceScope.right.right.left
    (And.intro coverUnary
      (And.intro sameCoverSpin
        (And.intro sourceScope.right.right.right.left sourceScope.right.right.right.right)))

theorem SpinGroupRootCarrier_public_boundary_transport_stability [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger product'
      boundary' spinEndpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame product product' ->
        hsame boundary boundary' ->
          Cont product' boundary' cliffordEndpoint ->
            Cont cliffordEndpoint groupWord spinEndpoint' ->
              SpinGroupRootCarrier unit vector product' boundary' cliffordEndpoint groupWord
                  spinEndpoint' ledger bundle pkg ∧ hsame spinEndpoint spinEndpoint' := by
  intro carrier sameProduct sameBoundary transportedBoundary transportedSpin
  have productUnary : UnaryHistory product :=
    unary_cont_closed carrier.left.right.left carrier.left.right.left
      carrier.left.right.right.right.left
  have productUnary' : UnaryHistory product' :=
    unary_transport productUnary sameProduct
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_transport carrier.left.right.right.left sameBoundary
  have clifford' :
      CliffordCarrierPackage unit vector product' boundary' cliffordEndpoint :=
    And.intro carrier.left.left
        (And.intro carrier.left.right.left
          (And.intro boundaryUnary'
          (And.intro (cont_result_hsame_transport carrier.left.right.right.right.left
            sameProduct) transportedBoundary)))
  have group' : GroupSingletonCarrier groupWord :=
    carrier.right.left
  have sameSpin : hsame spinEndpoint spinEndpoint' :=
    cont_respects_hsame (hsame_refl cliffordEndpoint) (hsame_refl groupWord)
      carrier.right.right.left transportedSpin
  exact And.intro
    (And.intro clifford'
      (And.intro group'
        (And.intro transportedSpin carrier.right.right.right)))
    sameSpin

theorem SpinGroupRootCarrier_double_cover_consumer_exhaustion [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame row spinEndpoint ->
        SemanticNameCert (fun h : BHist => hsame h row) (fun h : BHist => hsame h row)
          (fun h : BHist => hsame h row) hsame ∧
            CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
              GroupSingletonCarrier groupWord ∧ UnaryHistory row ∧ UnaryHistory spinEndpoint ∧
                Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier sameRowSpin
  have scope := SpinGroupRootCarrier_source_scope carrier
  have rowSelf : hsame row row :=
    hsame_refl row
  have rowUnary : UnaryHistory row :=
    unary_transport scope.right.right.left (hsame_symm sameRowSpin)
  have cert :
      SemanticNameCert (fun h : BHist => hsame h row) (fun h : BHist => hsame h row)
        (fun h : BHist => hsame h row) hsame := {
    core := {
      carrier_inhabited := Exists.intro row rowSelf
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK source
        exact hsame_trans (hsame_symm sameHK) source
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }
  exact
    And.intro cert
      (And.intro scope.left
        (And.intro scope.right.left
          (And.intro rowUnary
            (And.intro scope.right.right.left
              (And.intro scope.right.right.right.left scope.right.right.right.right)))))

theorem SpinGroupRootCarrier_transport_closure [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint cliffordEndpoint' groupWord groupWord'
      spinEndpoint spinEndpoint' ledger transportLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame cliffordEndpoint cliffordEndpoint' ->
        hsame groupWord groupWord' ->
          Cont product boundary cliffordEndpoint' ->
            Cont cliffordEndpoint' groupWord' spinEndpoint' ->
              Cont spinEndpoint' groupWord' transportLedger ->
                SpinGroupRootCarrier unit vector product boundary cliffordEndpoint' groupWord'
                    spinEndpoint' ledger bundle pkg ∧
                  hsame spinEndpoint spinEndpoint' ∧ UnaryHistory transportLedger ∧
                    hsame transportLedger (append spinEndpoint' groupWord') ∧
                      PkgSig bundle ledger pkg := by
  intro carrier sameClifford sameGroup productBoundary spinCont transportCont
  have transported :=
    SpinGroupRootCarrier_group_law_transport carrier sameClifford sameGroup productBoundary spinCont
  have transportedScope := SpinGroupRootCarrier_source_scope transported.left
  have groupUnary' : UnaryHistory groupWord' :=
    unary_transport unary_empty (hsame_symm transportedScope.right.left)
  have transportUnary : UnaryHistory transportLedger :=
    unary_cont_closed transportedScope.right.right.left groupUnary' transportCont
  exact And.intro transported.left
    (And.intro transported.right
      (And.intro transportUnary
        (And.intro transportCont transportedScope.right.right.right.right)))

end BEDC.Derived.SpinGroupUp
