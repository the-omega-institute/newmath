import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.InfCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def InfCatBHistSourcePacket [AskSetup] [PackageSetup]
    (simplicial category horn lift provenance transport : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory simplicial ∧ UnaryHistory category ∧ UnaryHistory horn ∧
    UnaryHistory lift ∧ UnaryHistory provenance ∧ Cont simplicial horn lift ∧
      Cont provenance lift transport ∧ PkgSig bundle transport pkg

theorem InfCatBHistSourcePacket_inner_horn_ledger_boundary [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      UnaryHistory simplicial ∧ UnaryHistory horn ∧ UnaryHistory lift ∧
        UnaryHistory provenance ∧ UnaryHistory transport ∧ Cont simplicial horn lift ∧
          Cont provenance lift transport ∧ hsame lift (append simplicial horn) ∧
            hsame transport (append provenance lift) ∧ PkgSig bundle transport pkg := by
  intro packet
  have simplicialUnary : UnaryHistory simplicial := packet.left
  have hornUnary : UnaryHistory horn := packet.right.right.left
  have liftUnary : UnaryHistory lift := packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.left
  have simplicialHornLift : Cont simplicial horn lift :=
    packet.right.right.right.right.right.left
  have provenanceLiftTransport : Cont provenance lift transport :=
    packet.right.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed provenanceUnary liftUnary provenanceLiftTransport
  exact And.intro simplicialUnary
    (And.intro hornUnary
      (And.intro liftUnary
        (And.intro provenanceUnary
          (And.intro transportUnary
            (And.intro simplicialHornLift
              (And.intro provenanceLiftTransport
                (And.intro simplicialHornLift
                  (And.intro provenanceLiftTransport
                    packet.right.right.right.right.right.right.right))))))))

theorem InfCatQuasicategoryClassifierSurface_transport [AskSetup] [PackageSetup]
    {category horn lifting provenance categoryHorn hornLifting endpoint category' horn'
      lifting' provenance' categoryHorn' hornLifting' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory category -> UnaryHistory horn -> UnaryHistory lifting ->
      UnaryHistory provenance -> Cont category horn categoryHorn ->
        Cont categoryHorn lifting hornLifting -> Cont provenance hornLifting endpoint ->
          PkgSig bundle endpoint pkg -> hsame category category' -> hsame horn horn' ->
            hsame lifting lifting' -> hsame provenance provenance' ->
              Cont category' horn' categoryHorn' ->
                Cont categoryHorn' lifting' hornLifting' ->
                  Cont provenance' hornLifting' endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      UnaryHistory categoryHorn' ∧ UnaryHistory hornLifting' ∧
                        hsame categoryHorn categoryHorn' ∧
                          hsame hornLifting hornLifting' ∧ hsame endpoint endpoint' ∧
                            PkgSig bundle endpoint' pkg := by
  intro categoryUnary hornUnary liftingUnary _provenanceUnary categoryHornCont hornLiftingCont
    endpointCont _pkgSig sameCategory sameHorn sameLifting sameProvenance categoryHornCont'
    hornLiftingCont' endpointCont' pkgSig'
  have categoryUnary' : UnaryHistory category' :=
    unary_transport categoryUnary sameCategory
  have hornUnary' : UnaryHistory horn' :=
    unary_transport hornUnary sameHorn
  have liftingUnary' : UnaryHistory lifting' :=
    unary_transport liftingUnary sameLifting
  have categoryHornUnary' : UnaryHistory categoryHorn' :=
    unary_cont_closed categoryUnary' hornUnary' categoryHornCont'
  have sameCategoryHorn : hsame categoryHorn categoryHorn' :=
    cont_respects_hsame sameCategory sameHorn categoryHornCont categoryHornCont'
  have hornLiftingUnary' : UnaryHistory hornLifting' :=
    unary_cont_closed categoryHornUnary' liftingUnary' hornLiftingCont'
  have sameHornLifting : hsame hornLifting hornLifting' :=
    cont_respects_hsame sameCategoryHorn sameLifting hornLiftingCont hornLiftingCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameHornLifting endpointCont endpointCont'
  exact
    ⟨categoryHornUnary', hornLiftingUnary', sameCategoryHorn, sameHornLifting,
      sameEndpoint, pkgSig'⟩

theorem InfCatBHistSourcePacket_quasicategory_classifier_surface [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport simplicial' category' horn' lift'
      provenance' transport' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      hsame simplicial simplicial' -> hsame category category' -> hsame horn horn' ->
        hsame provenance provenance' -> Cont simplicial' horn' lift' ->
          Cont provenance' lift' transport' -> PkgSig bundle transport' pkg ->
            InfCatBHistSourcePacket simplicial' category' horn' lift' provenance' transport'
                bundle pkg ∧
              hsame lift lift' ∧ hsame transport transport' := by
  intro packet sameSimplicial sameCategory sameHorn sameProvenance liftRow' transportRow'
    pkgRow'
  have liftSame : hsame lift lift' :=
    cont_respects_hsame sameSimplicial sameHorn packet.right.right.right.right.right.left
      liftRow'
  have transportSame : hsame transport transport' :=
    cont_respects_hsame sameProvenance liftSame packet.right.right.right.right.right.right.left
      transportRow'
  have targetPacket :
      InfCatBHistSourcePacket simplicial' category' horn' lift' provenance' transport'
        bundle pkg := by
    exact ⟨unary_transport packet.left sameSimplicial,
      unary_transport packet.right.left sameCategory,
      unary_transport packet.right.right.left sameHorn,
      unary_transport packet.right.right.right.left liftSame,
      unary_transport packet.right.right.right.right.left sameProvenance,
      liftRow',
      transportRow',
      pkgRow'⟩
  exact And.intro targetPacket (And.intro liftSame transportSame)

theorem InfCatBHistSourcePacket_consumer_boundary [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      Cont lift transport consumer ->
        UnaryHistory consumer ∧ hsame consumer (append lift transport) ∧
          UnaryHistory transport ∧ PkgSig bundle transport pkg := by
  intro packet consumerRow
  have liftUnary : UnaryHistory lift := packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.left
  have provenanceLiftTransport : Cont provenance lift transport :=
    packet.right.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed provenanceUnary liftUnary provenanceLiftTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed liftUnary transportUnary consumerRow
  exact ⟨consumerUnary, consumerRow, transportUnary,
    packet.right.right.right.right.right.right.right⟩

theorem InfCatBHistSourcePacket_provenance_transport_spine [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      Cont lift transport consumer ->
        hsame consumer (append lift (append provenance lift)) ∧ UnaryHistory consumer ∧
          PkgSig bundle transport pkg := by
  intro packet consumerRow
  have liftUnary : UnaryHistory lift := packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.left
  have provenanceLiftTransport : Cont provenance lift transport :=
    packet.right.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed provenanceUnary liftUnary provenanceLiftTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed liftUnary transportUnary consumerRow
  have sameSpine : hsame consumer (append lift (append provenance lift)) := by
    cases provenanceLiftTransport
    cases consumerRow
    rfl
  exact And.intro sameSpine
    (And.intro consumerUnary packet.right.right.right.right.right.right.right)

theorem InfCatBHistSourcePacket_inner_horn_consumer_determinacy [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport simplicial' category' horn' lift'
      provenance' transport' consumer consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      hsame simplicial simplicial' ->
        hsame category category' ->
          hsame horn horn' ->
            hsame provenance provenance' ->
              Cont simplicial' horn' lift' ->
                Cont provenance' lift' transport' ->
                  PkgSig bundle transport' pkg ->
                    Cont lift transport consumer ->
                      Cont lift' transport' consumer' ->
                        InfCatBHistSourcePacket simplicial' category' horn' lift'
                            provenance' transport' bundle pkg ∧
                          hsame lift lift' ∧ hsame transport transport' ∧
                            hsame consumer consumer' := by
  intro packet sameSimplicial sameCategory sameHorn sameProvenance liftRow' transportRow'
  intro pkgRow' consumerRow consumerRow'
  have transported :=
    InfCatBHistSourcePacket_quasicategory_classifier_surface packet sameSimplicial
      sameCategory sameHorn sameProvenance liftRow' transportRow' pkgRow'
  have sameConsumer : hsame consumer consumer' :=
    cont_respects_hsame transported.right.left transported.right.right consumerRow consumerRow'
  exact And.intro transported.left
    (And.intro transported.right.left
      (And.intro transported.right.right sameConsumer))

theorem InfCatBHistSourcePacket_public_certificate_boundary [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      Cont horn transport boundary ->
        UnaryHistory simplicial ∧ UnaryHistory category ∧ UnaryHistory horn ∧
          UnaryHistory lift ∧ UnaryHistory provenance ∧ UnaryHistory transport ∧
            UnaryHistory boundary ∧ PkgSig bundle transport pkg ∧
              hsame boundary (append horn transport) := by
  intro packet boundaryRow
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.left
  have liftUnary : UnaryHistory lift := packet.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed provenanceUnary liftUnary packet.right.right.right.right.right.right.left
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed packet.right.right.left transportUnary boundaryRow
  exact ⟨packet.left, packet.right.left, packet.right.right.left, liftUnary, provenanceUnary,
    transportUnary, boundaryUnary, packet.right.right.right.right.right.right.right, boundaryRow⟩

theorem InfCatBHistSourcePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      SemanticNameCert
        (fun t : BHist =>
          InfCatBHistSourcePacket simplicial category horn lift provenance t bundle pkg)
        (fun t : BHist =>
          InfCatBHistSourcePacket simplicial category horn lift provenance t bundle pkg)
        (fun t : BHist =>
          InfCatBHistSourcePacket simplicial category horn lift provenance t bundle pkg)
        (fun t u : BHist =>
          InfCatBHistSourcePacket simplicial category horn lift provenance t bundle pkg ∧
            InfCatBHistSourcePacket simplicial category horn lift provenance u bundle pkg ∧
              hsame t u) := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro transport packet
      equiv_refl := by
        intro row rowPacket
        exact And.intro rowPacket (And.intro rowPacket (hsame_refl row))
      equiv_symm := by
        intro row row' classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro row row' row'' classified classified'
        exact And.intro classified.left
          (And.intro classified'.right.left
            (hsame_trans classified.right.right classified'.right.right))
      carrier_respects_equiv := by
        intro row row' classified _rowPacket
        exact classified.right.left
    }
    pattern_sound := by
      intro _row rowPacket
      exact rowPacket
    ledger_sound := by
      intro _row rowPacket
      exact rowPacket
  }

theorem InfCatBHistSourcePacket_root_threshold_obligation_triad [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport dependencySurface finiteSurface
      rootSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      Cont simplicial category dependencySurface ->
        Cont horn lift finiteSurface ->
          Cont dependencySurface finiteSurface rootSurface ->
            UnaryHistory dependencySurface ∧ UnaryHistory finiteSurface ∧
              UnaryHistory rootSurface ∧ hsame dependencySurface (append simplicial category) ∧
                hsame finiteSurface (append horn lift) ∧
                  hsame rootSurface (append dependencySurface finiteSurface) ∧
                    PkgSig bundle transport pkg := by
  intro packet dependencyRow finiteRow rootRow
  obtain ⟨simplicialUnary, categoryUnary, hornUnary, liftUnary, _provenanceUnary,
    _liftCont, _transportCont, pkgSig⟩ := packet
  have dependencyUnary : UnaryHistory dependencySurface :=
    unary_cont_closed simplicialUnary categoryUnary dependencyRow
  have finiteUnary : UnaryHistory finiteSurface :=
    unary_cont_closed hornUnary liftUnary finiteRow
  have rootUnary : UnaryHistory rootSurface :=
    unary_cont_closed dependencyUnary finiteUnary rootRow
  exact
    ⟨dependencyUnary, finiteUnary, rootUnary, dependencyRow, finiteRow, rootRow,
      pkgSig⟩

theorem InfCatBHistSourcePacket_source_classifier_obligation_surface [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      exists dependencySurface : BHist, exists finiteSurface : BHist,
        exists rootSurface : BHist, exists consumerSurface : BHist,
          Cont simplicial category dependencySurface ∧ Cont horn lift finiteSurface ∧
            Cont dependencySurface finiteSurface rootSurface ∧
              Cont rootSurface transport consumerSurface ∧
                UnaryHistory dependencySurface ∧ UnaryHistory finiteSurface ∧
                  UnaryHistory rootSurface ∧ UnaryHistory consumerSurface ∧
                    hsame consumerSurface (append rootSurface transport) ∧
                      PkgSig bundle transport pkg := by
  intro packet
  obtain ⟨simplicialUnary, categoryUnary, hornUnary, liftUnary, provenanceUnary,
    _liftRow, provenanceTransportRow, pkgSig⟩ := packet
  let dependencySurface := append simplicial category
  let finiteSurface := append horn lift
  let rootSurface := append dependencySurface finiteSurface
  let consumerSurface := append rootSurface transport
  have dependencyRow : Cont simplicial category dependencySurface := by
    rfl
  have finiteRow : Cont horn lift finiteSurface := by
    rfl
  have rootRow : Cont dependencySurface finiteSurface rootSurface := by
    rfl
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed provenanceUnary liftUnary provenanceTransportRow
  have consumerRow : Cont rootSurface transport consumerSurface := by
    rfl
  have dependencyUnary : UnaryHistory dependencySurface :=
    unary_cont_closed simplicialUnary categoryUnary dependencyRow
  have finiteUnary : UnaryHistory finiteSurface :=
    unary_cont_closed hornUnary liftUnary finiteRow
  have rootUnary : UnaryHistory rootSurface :=
    unary_cont_closed dependencyUnary finiteUnary rootRow
  have consumerUnary : UnaryHistory consumerSurface :=
    unary_cont_closed rootUnary transportUnary consumerRow
  exact
    ⟨dependencySurface, finiteSurface, rootSurface, consumerSurface, dependencyRow,
      finiteRow, rootRow, consumerRow, dependencyUnary, finiteUnary, rootUnary,
      consumerUnary, consumerRow, pkgSig⟩

theorem InfCatBHistSourcePacket_source_classifier_obligations [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport simplicial' category' horn' lift'
      provenance' transport' consumer boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      hsame simplicial simplicial' -> hsame category category' -> hsame horn horn' ->
        hsame provenance provenance' -> Cont simplicial' horn' lift' ->
          Cont provenance' lift' transport' -> PkgSig bundle transport' pkg ->
            Cont lift' transport' consumer -> Cont horn' transport' boundary ->
              InfCatBHistSourcePacket simplicial' category' horn' lift' provenance' transport'
                  bundle pkg ∧
                hsame lift lift' ∧ hsame transport transport' ∧ UnaryHistory consumer ∧
                  UnaryHistory boundary := by
  intro packet sameSimplicial sameCategory sameHorn sameProvenance liftRow' transportRow'
    pkgRow' consumerRow boundaryRow
  have transported :=
    InfCatBHistSourcePacket_quasicategory_classifier_surface packet sameSimplicial
      sameCategory sameHorn sameProvenance liftRow' transportRow' pkgRow'
  have liftUnary' : UnaryHistory lift' :=
    transported.left.right.right.right.left
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed transported.left.right.right.right.right.left liftUnary' transportRow'
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed liftUnary' transportUnary' consumerRow
  have hornUnary' : UnaryHistory horn' :=
    transported.left.right.right.left
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed hornUnary' transportUnary' boundaryRow
  exact
    ⟨transported.left, transported.right.left, transported.right.right, consumerUnary,
      boundaryUnary⟩

theorem InfCatBHistSourcePacket_stability_exactness_ledger_obligations [AskSetup]
    [PackageSetup]
    {simplicial category horn lift provenance transport simplicial' category' horn' lift'
      provenance' transport' consumer consumer' boundary boundary' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      hsame simplicial simplicial' -> hsame category category' -> hsame horn horn' ->
        hsame provenance provenance' -> Cont simplicial' horn' lift' ->
          Cont provenance' lift' transport' -> PkgSig bundle transport' pkg ->
            Cont lift transport consumer -> Cont lift' transport' consumer' ->
              Cont horn transport boundary -> Cont horn' transport' boundary' ->
                InfCatBHistSourcePacket simplicial' category' horn' lift' provenance'
                    transport' bundle pkg ∧
                  hsame lift lift' ∧ hsame transport transport' ∧
                    hsame consumer consumer' ∧ hsame boundary boundary' ∧
                      UnaryHistory consumer' ∧ UnaryHistory boundary' := by
  intro packet sameSimplicial sameCategory sameHorn sameProvenance liftRow'
    transportRow' pkgRow' consumerRow consumerRow' boundaryRow boundaryRow'
  have transported :=
    InfCatBHistSourcePacket_quasicategory_classifier_surface packet sameSimplicial
      sameCategory sameHorn sameProvenance liftRow' transportRow' pkgRow'
  have sameConsumer : hsame consumer consumer' :=
    cont_respects_hsame transported.right.left transported.right.right consumerRow consumerRow'
  have sameBoundary : hsame boundary boundary' :=
    cont_respects_hsame sameHorn transported.right.right boundaryRow boundaryRow'
  have liftUnary' : UnaryHistory lift' :=
    transported.left.right.right.right.left
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed transported.left.right.right.right.right.left liftUnary' transportRow'
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed liftUnary' transportUnary' consumerRow'
  have hornUnary' : UnaryHistory horn' :=
    transported.left.right.right.left
  have boundaryUnary' : UnaryHistory boundary' :=
    unary_cont_closed hornUnary' transportUnary' boundaryRow'
  exact
    ⟨transported.left, transported.right.left, transported.right.right, sameConsumer,
      sameBoundary, consumerUnary', boundaryUnary'⟩

theorem InfCatBHistSourcePacket_obligation_inventory_fields [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      Cont horn transport boundary ->
        UnaryHistory simplicial ∧ UnaryHistory category ∧ UnaryHistory horn ∧
          UnaryHistory lift ∧ UnaryHistory provenance ∧ UnaryHistory transport ∧
            UnaryHistory boundary ∧ Cont simplicial horn lift ∧ Cont provenance lift transport ∧
              hsame boundary (append horn transport) ∧ PkgSig bundle transport pkg := by
  intro packet boundaryRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed packet.right.right.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.left
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed packet.right.right.left transportUnary boundaryRow
  exact
    ⟨packet.left, packet.right.left, packet.right.right.left, packet.right.right.right.left,
      packet.right.right.right.right.left, transportUnary, boundaryUnary,
      packet.right.right.right.right.right.left, packet.right.right.right.right.right.right.left,
      boundaryRow, packet.right.right.right.right.right.right.right⟩

end BEDC.Derived.InfCatUp
