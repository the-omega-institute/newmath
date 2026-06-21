import BEDC.Derived.BoundedNormalEqualityCheckerUp
import BEDC.Derived.MetaCICDecidableBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICDecidableBoundaryCarrier [AskSetup] [PackageSetup]
    (checker structural bounded finished refusal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory checker ∧ UnaryHistory structural ∧ UnaryHistory finished ∧
    UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont checker structural bounded ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem MetaCICDecidableBoundary_sibling_provenance [AskSetup] [PackageSetup]
    {checker structural bounded finished refusal transport replay provenance localName
      siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier checker structural bounded finished refusal transport replay
        provenance localName bundle pkg →
      Cont provenance replay siblingRead →
        PkgSig bundle siblingRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row provenance ∨ hsame row siblingRead ∨
                  Cont provenance replay siblingRead)
              (fun _ : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle siblingRead pkg)
              hsame ∧
            UnaryHistory siblingRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier provenanceReplaySibling siblingPkg
  obtain ⟨_checkerUnary, _structuralUnary, _finishedUnary, _refusalUnary, _transportUnary,
    replayUnary, provenanceUnary, _localNameUnary, _checkerStructuralBounded,
    provenancePkg, _localNamePkg⟩ := carrier
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed provenanceUnary replayUnary provenanceReplaySibling
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row siblingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row provenance ∨ hsame row siblingRead ∨
              Cont provenance replay siblingRead)
          (fun row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle siblingRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro siblingRead ⟨hsame_refl siblingRead, siblingUnary⟩
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _ _source
      exact ⟨provenancePkg, siblingPkg⟩
  }
  exact ⟨cert, siblingUnary⟩

theorem MetaCICDecidableBoundary_bounded_checker_scope_handoff [AskSetup] [PackageSetup]
    {checker structural bounded finished refusal transport replay provenance localName
      left right fuel normalLeft normalRight equality witness closed checkerTransport checkerRoute
      checkerProvenance checkerNameCert checkerPackageRead boundarySiblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier checker structural bounded finished refusal transport replay
        provenance localName bundle pkg →
      BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier left right
          fuel normalLeft normalRight equality witness closed checkerTransport checkerRoute
          checkerProvenance checkerNameCert bundle pkg →
        Cont checkerTransport checkerRoute checkerPackageRead →
          hsame checkerPackageRead bounded →
            Cont provenance replay boundarySiblingRead →
              PkgSig bundle boundarySiblingRead pkg →
                (∀ row : BHist,
                    hsame row checkerPackageRead ∧ UnaryHistory row →
                      hsame row left ∨ hsame row right ∨ hsame row fuel ∨
                        hsame row normalLeft ∨ hsame row normalRight ∨ hsame row equality ∨
                          hsame row witness ∨ hsame row closed ∨ hsame row checkerTransport ∨
                            hsame row checkerRoute ∨ hsame row checkerProvenance ∨
                              hsame row checkerNameCert ∨ hsame row checkerPackageRead) ∧
                  (∀ row : BHist,
                    hsame row checkerPackageRead ∧ UnaryHistory row →
                      UnaryHistory row ∧ Cont left fuel normalLeft ∧
                        Cont right fuel normalRight ∧ Cont normalLeft normalRight equality ∧
                          Cont checkerTransport checkerRoute checkerPackageRead ∧
                            PkgSig bundle checkerProvenance pkg ∧
                              PkgSig bundle checkerNameCert pkg) ∧
                    SemanticNameCert
                        (fun row : BHist => hsame row boundarySiblingRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row provenance ∨ hsame row boundarySiblingRead ∨
                            Cont provenance replay boundarySiblingRead)
                        (fun _ : BHist =>
                          PkgSig bundle provenance pkg ∧ PkgSig bundle boundarySiblingRead pkg)
                        hsame ∧
                      UnaryHistory bounded ∧ UnaryHistory boundarySiblingRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro boundaryCarrier checkerCarrier checkerPackageRoute checkerPackageSame
    provenanceReplaySibling siblingPkg
  have checkerScope :=
    BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier_scope_closure
      checkerCarrier checkerPackageRoute
  have siblingScope :=
    MetaCICDecidableBoundary_sibling_provenance boundaryCarrier provenanceReplaySibling siblingPkg
  have boundedUnary : UnaryHistory bounded :=
    unary_transport checkerScope.right.left checkerPackageSame
  exact
    ⟨fun row source => checkerScope.left.pattern_sound source,
      fun row source => checkerScope.left.ledger_sound source,
      siblingScope.left, boundedUnary, siblingScope.right⟩

theorem MetaCICDecidableBoundary_bounded_checker_fuel_handoff [AskSetup] [PackageSetup]
    {checker structural bounded finished refusal transport replay provenance localName left right fuel
      fuelPlus normalLeft normalRight equality witness closed checkerTransport checkerRoute
      checkerProvenance checkerNameCert normalLeftPlus normalRightPlus equalityPlus witnessPlus
      closedPlus checkerTransportPlus checkerRoutePlus checkerProvenancePlus checkerNameCertPlus
      boundarySiblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier checker structural bounded finished refusal transport replay
        provenance localName bundle pkg →
      BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier left right
          fuel normalLeft normalRight equality witness closed checkerTransport checkerRoute
          checkerProvenance checkerNameCert bundle pkg →
        BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier left right
            fuelPlus normalLeftPlus normalRightPlus equalityPlus witnessPlus closedPlus
            checkerTransportPlus checkerRoutePlus checkerProvenancePlus checkerNameCertPlus
            bundle pkg →
          hsame fuel fuelPlus →
            Cont normalLeftPlus normalRightPlus equalityPlus →
              Cont equalityPlus witnessPlus checkerRoutePlus →
                hsame checkerRoutePlus bounded →
                  Cont provenance replay boundarySiblingRead →
                    PkgSig bundle boundarySiblingRead pkg →
                      UnaryHistory bounded ∧ UnaryHistory fuelPlus ∧
                        UnaryHistory normalLeftPlus ∧ UnaryHistory normalRightPlus ∧
                          UnaryHistory equalityPlus ∧ UnaryHistory checkerRoutePlus ∧
                            Cont normalLeftPlus normalRightPlus equalityPlus ∧
                              Cont equalityPlus witnessPlus checkerRoutePlus ∧
                                PkgSig bundle checkerProvenancePlus pkg ∧
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row boundarySiblingRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row provenance ∨
                                          hsame row boundarySiblingRead ∨
                                            Cont provenance replay boundarySiblingRead)
                                      (fun _ : BHist =>
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle boundarySiblingRead pkg)
                                      hsame ∧
                                    UnaryHistory boundarySiblingRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro boundaryCarrier checkerCarrier checkerCarrierPlus fuelSame equalityPlusRoute
    checkerRoutePlusRoute checkerRoutePlusSame provenanceReplaySibling siblingPkg
  have fuelScope :=
    BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier_fuel_monotonicity
      checkerCarrier checkerCarrierPlus fuelSame equalityPlusRoute checkerRoutePlusRoute
  have siblingScope :=
    MetaCICDecidableBoundary_sibling_provenance boundaryCarrier provenanceReplaySibling siblingPkg
  obtain ⟨_leftUnary, _rightUnary, _fuelUnary, fuelPlusUnary, normalLeftPlusUnary,
    normalRightPlusUnary, equalityPlusUnary, checkerRoutePlusUnary, equalityPlusRouteRead,
    checkerRoutePlusRouteRead, checkerProvenancePlusPkg⟩ := fuelScope
  have boundedUnary : UnaryHistory bounded :=
    unary_transport checkerRoutePlusUnary checkerRoutePlusSame
  exact
    ⟨boundedUnary, fuelPlusUnary, normalLeftPlusUnary, normalRightPlusUnary,
      equalityPlusUnary, checkerRoutePlusUnary, equalityPlusRouteRead, checkerRoutePlusRouteRead,
      checkerProvenancePlusPkg, siblingScope.left, siblingScope.right⟩

theorem MetaCICDecidableBoundary_bounded_checker_readback_handoff [AskSetup] [PackageSetup]
    {checker structural bounded finished refusal transport replay provenance localName left right fuel
      normalLeft normalRight equality witness closed checkerTransport checkerRoute checkerProvenance
      checkerNameCert normalLeftRead normalRightRead equalityRead finishedRead
      boundarySiblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier checker structural bounded finished refusal transport replay
        provenance localName bundle pkg →
      BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier left right
          fuel normalLeft normalRight equality witness closed checkerTransport checkerRoute
          checkerProvenance checkerNameCert bundle pkg →
        hsame normalLeftRead normalLeft →
          hsame normalRightRead normalRight →
            hsame equalityRead equality →
              Cont normalLeftRead normalRightRead equalityRead →
                Cont equalityRead witness finishedRead →
                  hsame finishedRead bounded →
                    Cont provenance replay boundarySiblingRead →
                      PkgSig bundle boundarySiblingRead pkg →
                        UnaryHistory bounded ∧ UnaryHistory normalLeftRead ∧
                          UnaryHistory normalRightRead ∧ UnaryHistory equalityRead ∧
                            UnaryHistory finishedRead ∧
                              Cont normalLeftRead normalRightRead equalityRead ∧
                                Cont equalityRead witness finishedRead ∧
                                  PkgSig bundle checkerProvenance pkg ∧
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row boundarySiblingRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row provenance ∨
                                            hsame row boundarySiblingRead ∨
                                              Cont provenance replay boundarySiblingRead)
                                        (fun _ : BHist =>
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle boundarySiblingRead pkg)
                                        hsame ∧
                                      UnaryHistory boundarySiblingRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro boundaryCarrier checkerCarrier normalLeftSame normalRightSame equalitySame
    equalityReadRoute finishedReadRoute finishedBoundedSame provenanceReplaySibling siblingPkg
  have readbackScope :=
    BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier_deterministic_normal_form_readback
      checkerCarrier normalLeftSame normalRightSame equalitySame equalityReadRoute finishedReadRoute
  have siblingScope :=
    MetaCICDecidableBoundary_sibling_provenance boundaryCarrier provenanceReplaySibling siblingPkg
  obtain ⟨normalLeftReadUnary, normalRightReadUnary, equalityReadUnary, finishedReadUnary,
    equalityReadRouteRead, finishedReadRouteRead, checkerProvenancePkg⟩ := readbackScope
  have boundedUnary : UnaryHistory bounded :=
    unary_transport finishedReadUnary finishedBoundedSame
  exact
    ⟨boundedUnary, normalLeftReadUnary, normalRightReadUnary, equalityReadUnary, finishedReadUnary,
      equalityReadRouteRead, finishedReadRouteRead, checkerProvenancePkg, siblingScope.left,
      siblingScope.right⟩

theorem MetaCICDecidableBoundary_bounded_checker_consumer_handoff [AskSetup] [PackageSetup]
    {checker structural bounded finished refusal transport replay provenance localName left right fuel
      normalLeft normalRight equality witness closed checkerTransport checkerRoute checkerProvenance
      checkerNameCert equalityRead finishedRead localRead boundarySiblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier checker structural bounded finished refusal transport replay
        provenance localName bundle pkg →
      BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier left right
          fuel normalLeft normalRight equality witness closed checkerTransport checkerRoute
          checkerProvenance checkerNameCert bundle pkg →
        Cont normalLeft normalRight equalityRead →
          Cont equalityRead witness finishedRead →
            hsame localRead checkerNameCert →
              UnaryHistory localRead →
                hsame finishedRead bounded →
                  Cont provenance replay boundarySiblingRead →
                    PkgSig bundle boundarySiblingRead pkg →
                      UnaryHistory bounded ∧ UnaryHistory boundarySiblingRead ∧
                        UnaryHistory localRead ∧ Cont normalLeft normalRight equalityRead ∧
                          Cont equalityRead witness finishedRead ∧
                            PkgSig bundle checkerProvenance pkg ∧
                              PkgSig bundle checkerNameCert pkg ∧
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row boundarySiblingRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row provenance ∨ hsame row boundarySiblingRead ∨
                                        Cont provenance replay boundarySiblingRead)
                                    (fun _ : BHist =>
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle boundarySiblingRead pkg)
                                    hsame := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro boundaryCarrier checkerCarrier equalityReadRoute finishedReadRoute localSame localUnary
    finishedBoundedSame provenanceReplaySibling siblingPkg
  have consumerScope :=
    BEDC.Derived.BoundedNormalEqualityCheckerUp.BoundedNormalEqualityCheckerCarrier_consumer_nonescape
      checkerCarrier equalityReadRoute finishedReadRoute localSame localUnary
  have siblingScope :=
    MetaCICDecidableBoundary_sibling_provenance boundaryCarrier provenanceReplaySibling siblingPkg
  obtain ⟨_leftUnary, _rightUnary, _fuelUnary, _normalLeftUnary, _normalRightUnary,
    _equalityUnary, _equalityReadUnary, finishedReadUnary, _equalityRoute,
    equalityReadRouteRead, finishedReadRouteRead, checkerProvenancePkg, checkerNameCertPkg⟩ :=
      consumerScope
  have boundedUnary : UnaryHistory bounded :=
    unary_transport finishedReadUnary finishedBoundedSame
  exact
    ⟨boundedUnary, siblingScope.right, localUnary, equalityReadRouteRead, finishedReadRouteRead,
      checkerProvenancePkg, checkerNameCertPkg, siblingScope.left⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
