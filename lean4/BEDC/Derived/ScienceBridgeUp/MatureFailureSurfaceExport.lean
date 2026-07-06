import BEDC.Derived.GapFailureBridgeAuditUp.NameCertObligations
import BEDC.Derived.ScienceBridgeUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ScienceBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.GapFailureBridgeAuditUp

theorem ScienceBridgeMatureFailureSurfaceExport [AskSetup] [PackageSetup]
    {R O A T B G F H C P N objectRead auditRead truthRead bridgeRead gapRead
      failureRead preservedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ScienceBridgeUp →
      UnaryHistory R → UnaryHistory O → UnaryHistory A → UnaryHistory T →
        UnaryHistory B → UnaryHistory G → UnaryHistory F → UnaryHistory H →
          UnaryHistory N →
            Cont R O objectRead → Cont objectRead A auditRead →
              Cont auditRead T truthRead → Cont truthRead B bridgeRead →
                Cont bridgeRead G gapRead → Cont gapRead F failureRead →
                  Cont failureRead H preservedRead → Cont preservedRead N namedRead →
                    PkgSig bundle P pkg →
                      SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row R ∨ hsame row O ∨ hsame row A ∨ hsame row T ∨
                            hsame row B ∨ hsame row G ∨ hsame row F ∨
                              hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont R O objectRead ∧
                            Cont objectRead A auditRead ∧
                              Cont auditRead T truthRead ∧
                                Cont truthRead B bridgeRead ∧
                                  Cont bridgeRead G gapRead ∧
                                    Cont gapRead F failureRead ∧
                                      Cont failureRead H preservedRead ∧
                                        Cont preservedRead N namedRead ∧
                                          PkgSig bundle P pkg)
                        hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: ScienceBridgeUp BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _scienceBridge unaryR unaryO unaryA unaryT unaryB unaryG unaryF unaryH unaryN
    objectRoute auditRoute truthRoute bridgeRoute gapRoute failureRoute preservedRoute namedRoute
    packageRead
  have _replayRow : BHist := C
  have objectUnary : UnaryHistory objectRead :=
    unary_cont_closed unaryR unaryO objectRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed objectUnary unaryA auditRoute
  have truthUnary : UnaryHistory truthRead :=
    unary_cont_closed auditUnary unaryT truthRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed truthUnary unaryB bridgeRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed bridgeUnary unaryG gapRoute
  have failureUnary : UnaryHistory failureRead :=
    unary_cont_closed gapUnary unaryF failureRoute
  have preservedUnary : UnaryHistory preservedRead :=
    unary_cont_closed failureUnary unaryH preservedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed preservedUnary unaryN namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row R ∨ hsame row O ∨ hsame row A ∨ hsame row T ∨ hsame row B ∨
            hsame row G ∨ hsame row F ∨ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont R O objectRead ∧ Cont objectRead A auditRead ∧
            Cont auditRead T truthRead ∧ Cont truthRead B bridgeRead ∧
              Cont bridgeRead G gapRead ∧ Cont gapRead F failureRead ∧
                Cont failureRead H preservedRead ∧ Cont preservedRead N namedRead ∧
                  PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, objectRoute, auditRoute, truthRoute, bridgeRoute, gapRoute,
          failureRoute, preservedRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

theorem ScienceBridgeGapFailureAuditNonescapeHandoff [AskSetup] [PackageSetup]
    {R O A S B G F H C P N objectRead scienceAuditRead truthRead bridgeRead gapRead
      failureRead preservedRead namedRead L X gapFailureRead auditRouteRead gapAuditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ScienceBridgeUp ->
      UnaryHistory R -> UnaryHistory O -> UnaryHistory A -> UnaryHistory S ->
        UnaryHistory B -> UnaryHistory G -> UnaryHistory F -> UnaryHistory H ->
          UnaryHistory N ->
            Cont R O objectRead -> Cont objectRead A scienceAuditRead ->
              Cont scienceAuditRead S truthRead -> Cont truthRead B bridgeRead ->
                Cont bridgeRead G gapRead -> Cont gapRead F failureRead ->
                  Cont failureRead H preservedRead -> Cont preservedRead N namedRead ->
                    Cont B X auditRouteRead ->
                      Cont G F gapFailureRead ->
                        Cont gapFailureRead auditRouteRead gapAuditRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle gapAuditRead pkg ->
                              SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row O ∨ hsame row A ∨ hsame row S ∨
                                  hsame row B ∨ hsame row G ∨ hsame row F ∨
                                    hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont R O objectRead ∧
                                  Cont objectRead A scienceAuditRead ∧
                                    Cont scienceAuditRead S truthRead ∧
                                      Cont truthRead B bridgeRead ∧
                                        Cont bridgeRead G gapRead ∧
                                          Cont gapRead F failureRead ∧
                                            Cont failureRead H preservedRead ∧
                                              Cont preservedRead N namedRead ∧
                                                PkgSig bundle P pkg)
                              hsame ∧
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row gapAuditRead ∧ PkgSig bundle gapAuditRead pkg)
                                (fun row : BHist =>
                                  hsame row G ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨
                                    hsame row X ∨
                                      Cont G F gapFailureRead ∨ Cont B X auditRouteRead)
                                (fun row : BHist =>
                                  hsame row gapAuditRead ∧ PkgSig bundle gapAuditRead pkg)
                                hsame ∧
                              List.Mem (gapFailureBridgeAuditEncodeBHist G)
                                (gapFailureBridgeAuditToEventFlow
                                  (GapFailureBridgeAuditUp.mk G F B L X A H C P N)) ∧
                              List.Mem (gapFailureBridgeAuditEncodeBHist F)
                                (gapFailureBridgeAuditToEventFlow
                                  (GapFailureBridgeAuditUp.mk G F B L X A H C P N)) ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: ScienceBridgeUp GapFailureBridgeAuditUp BHist Cont Pkg SemanticNameCert UnaryHistory
  intro scienceBridge unaryR unaryO unaryA unaryS unaryB unaryG unaryF unaryH unaryN
    objectRoute scienceAuditRoute truthRoute bridgeRoute gapRoute failureRoute preservedRoute
    namedRoute bridgeAxisRoute gapFailureRoute gapAuditRoute packageRead gapAuditPkg
  have scienceExport :=
    ScienceBridgeMatureFailureSurfaceExport
      (R := R) (O := O) (A := A) (T := S) (B := B) (G := G) (F := F) (H := H)
      (C := C) (P := P) (N := N) (objectRead := objectRead)
      (auditRead := scienceAuditRead) (truthRead := truthRead) (bridgeRead := bridgeRead)
      (gapRead := gapRead) (failureRead := failureRead) (preservedRead := preservedRead)
      (namedRead := namedRead) (bundle := bundle) (pkg := pkg)
      scienceBridge unaryR unaryO unaryA unaryS unaryB unaryG unaryF unaryH unaryN
      objectRoute scienceAuditRoute truthRoute bridgeRoute gapRoute failureRoute
      preservedRoute namedRoute packageRead
  have gapAudit :=
    BEDC.Derived.GapFailureBridgeAuditUp.GapFailureBridgeAuditPacket_nonescape
      (T := G) (F := F) (B := B) (L := L) (X := X) (A := A) (H := H) (C := C)
      (P := P) (N := N) (gapFailure := gapFailureRead) (bridgeAxis := auditRouteRead)
      (auditRead := gapAuditRead) (bundle := bundle) (pkg := pkg)
      gapFailureRoute bridgeAxisRoute gapAuditRoute gapAuditPkg
  exact ⟨scienceExport.left, gapAudit.left, gapAudit.right.left, gapAudit.right.right.left,
    scienceExport.right⟩

end BEDC.Derived.ScienceBridgeUp
