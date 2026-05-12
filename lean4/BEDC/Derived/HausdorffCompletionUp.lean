import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HausdorffCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HausdorffCompletionCarrier [AskSetup] [PackageSetup]
    (source entourage separated handoff transport route provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory separated ∧
    UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ Cont source entourage transport ∧
        Cont separated handoff route ∧ Cont transport route provenance ∧
          PkgSig bundle provenance pkg

theorem HausdorffCompletionCarrier_classifier_transport [AskSetup] [PackageSetup]
    {source entourage separated handoff transport route provenance source' entourage'
      separated' handoff' transport' route' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionCarrier source entourage separated handoff transport route provenance
        bundle pkg ->
      hsame source source' ->
        hsame entourage entourage' ->
          hsame separated separated' ->
            hsame handoff handoff' ->
              hsame transport transport' ->
                Cont separated' handoff' route' ->
                  Cont transport' route' provenance' ->
                    PkgSig bundle provenance' pkg ->
                      HausdorffCompletionCarrier source' entourage' separated' handoff'
                          transport' route' provenance' bundle pkg ∧
                        hsame route route' := by
  intro carrier sameSource sameEntourage sameSeparated sameHandoff sameTransport routeRow'
    provenanceRow' provenancePkg'
  obtain ⟨sourceUnary, entourageUnary, separatedUnary, handoffUnary, transportUnary, routeUnary,
    provenanceUnary, sourceEntourageRow, routeRow, provenanceRow, _provenancePkg⟩ := carrier
  have transportRow' : Cont source' entourage' transport' :=
    cont_intro
      (sameTransport.symm.trans
        (cont_respects_hsame sameSource sameEntourage sourceEntourageRow (cont_intro rfl)))
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameSeparated sameHandoff routeRow routeRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameRoute provenanceRow provenanceRow'
  have sourceUnary' : UnaryHistory source' := unary_transport sourceUnary sameSource
  have entourageUnary' : UnaryHistory entourage' := unary_transport entourageUnary sameEntourage
  have separatedUnary' : UnaryHistory separated' := unary_transport separatedUnary sameSeparated
  have handoffUnary' : UnaryHistory handoff' := unary_transport handoffUnary sameHandoff
  have transportUnary' : UnaryHistory transport' := unary_transport transportUnary sameTransport
  have routeUnary' : UnaryHistory route' := unary_transport routeUnary sameRoute
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  exact
    ⟨⟨sourceUnary', entourageUnary', separatedUnary', handoffUnary', transportUnary',
        routeUnary', provenanceUnary', transportRow', routeRow', provenanceRow',
        provenancePkg'⟩,
      sameRoute⟩

def HausdorffCompletionPacket [AskSetup] [PackageSetup]
    (source entourage sealRow handoff transports routes provenance nameRow exported : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory entourage ∧ UnaryHistory handoff ∧
    UnaryHistory routes ∧ UnaryHistory nameRow ∧ Cont source entourage sealRow ∧
      Cont sealRow handoff transports ∧ Cont transports routes provenance ∧
        Cont provenance nameRow exported ∧ PkgSig bundle exported pkg

theorem HausdorffCompletionPacket_namecert_obligations [AskSetup] [PackageSetup]
    {source entourage sealRow handoff transports routes provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffCompletionPacket source entourage sealRow handoff transports routes provenance
        nameRow exported bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont provenance nameRow row ∧
          Cont source entourage sealRow ∧ Cont sealRow handoff transports)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont transports routes provenance ∧
          Cont provenance nameRow exported)
        (fun row row' : BHist => hsame row row') := by
  intro packet
  obtain ⟨sourceUnary, entourageUnary, handoffUnary, routesUnary, nameRowUnary,
    sourceEntourageSeal, sealHandoffTransports, transportsRoutesProvenance,
    provenanceNameExported, exportedPkg⟩ := packet
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed sourceUnary entourageUnary sourceEntourageSeal
  have transportsUnary : UnaryHistory transports :=
    unary_cont_closed sealRowUnary handoffUnary sealHandoffTransports
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportsUnary routesUnary transportsRoutesProvenance
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed provenanceUnary nameRowUnary provenanceNameExported
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportedPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport provenanceNameExported (hsame_symm sourceRow.left),
          sourceEntourageSeal, sealHandoffTransports⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, transportsRoutesProvenance, provenanceNameExported⟩
  }

end BEDC.Derived.HausdorffCompletionUp
