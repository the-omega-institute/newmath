import BEDC.Derived.GapFailureBridgeAuditUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.GapFailureBridgeAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem GapFailureBridgeAuditPacket_namecert_obligations [AskSetup] [PackageSetup]
    {T F B L X A H C P N gapFailure bridgeAxis auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T F gapFailure ->
      Cont B X bridgeAxis ->
        Cont gapFailure bridgeAxis auditRead ->
          PkgSig bundle auditRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row auditRead ∧
                  FieldFaithful.fields (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
                    [T, F, B, L, X, A, H, C, P, N])
              (fun row : BHist =>
                hsame row T ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨ hsame row X ∨
                  Cont T F gapFailure ∨ Cont B X bridgeAxis)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
              FieldFaithful.fields (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
                [T, F, B, L, X, A, H, C, P, N] ∧
              Cont T F gapFailure ∧
                Cont B X bridgeAxis ∧
                  Cont gapFailure bridgeAxis auditRead ∧
                    PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro gapRoute bridgeRoute auditRoute auditPkg
  have fields_eq :
      FieldFaithful.fields (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
        [T, F, B, L, X, A, H, C, P, N] := by
    rfl
  have sourceAudit :
      (fun row : BHist =>
        hsame row auditRead ∧
          FieldFaithful.fields (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
            [T, F, B, L, X, A, H, C, P, N]) auditRead := by
    exact ⟨hsame_refl auditRead, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row auditRead ∧
            FieldFaithful.fields (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
              [T, F, B, L, X, A, H, C, P, N])
        (fun row : BHist =>
          hsame row T ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨ hsame row X ∨
            Cont T F gapFailure ∨ Cont B X bridgeAxis)
        (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro auditRead sourceAudit
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row _source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl gapRoute)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, auditPkg⟩
    }
  exact ⟨cert, fields_eq, gapRoute, bridgeRoute, auditRoute, auditPkg⟩

theorem GapFailureBridgeAuditPacket_axis_separation [AskSetup] [PackageSetup]
    {T F B L X A H C P N gapFailure bridgeAxis auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T F gapFailure ->
      Cont B X bridgeAxis ->
        Cont gapFailure bridgeAxis auditRead ->
          PkgSig bundle auditRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row auditRead ∧
                  FieldFaithful.fields (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
                    [T, F, B, L, X, A, H, C, P, N])
              (fun row : BHist =>
                hsame row T ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨ hsame row X ∨
                  Cont T F gapFailure ∨ Cont B X bridgeAxis)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
              List.Mem (gapFailureBridgeAuditEncodeBHist X)
                (gapFailureBridgeAuditToEventFlow
                  (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) ∧
              Cont B X bridgeAxis := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro gapRoute bridgeRoute auditRoute auditPkg
  have obligations :=
    GapFailureBridgeAuditPacket_namecert_obligations
      (T := T) (F := F) (B := B) (L := L) (X := X) (A := A) (H := H) (C := C)
      (P := P) (N := N) (gapFailure := gapFailure) (bridgeAxis := bridgeAxis)
      (auditRead := auditRead) (bundle := bundle) (pkg := pkg)
      gapRoute bridgeRoute auditRoute auditPkg
  have xEncoded :
      List.Mem (gapFailureBridgeAuditEncodeBHist X)
        (gapFailureBridgeAuditToEventFlow
          (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) := by
    change
      List.Mem (gapFailureBridgeAuditEncodeBHist X)
        [[BMark.b0], gapFailureBridgeAuditEncodeBHist T, [BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist F, [BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist L,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist X,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist A,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          gapFailureBridgeAuditEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist N]
    exact
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))
  exact ⟨obligations.left, xEncoded, bridgeRoute⟩

theorem GapFailureBridgeAuditPacket_nonescape [AskSetup] [PackageSetup]
    {T F B L X A H C P N gapFailure bridgeAxis auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T F gapFailure ->
      Cont B X bridgeAxis ->
        Cont gapFailure bridgeAxis auditRead ->
          PkgSig bundle auditRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              (fun row : BHist =>
                hsame row T ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨ hsame row X ∨
                  Cont T F gapFailure ∨ Cont B X bridgeAxis)
              (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
              hsame ∧
              List.Mem (gapFailureBridgeAuditEncodeBHist T)
                (gapFailureBridgeAuditToEventFlow
                  (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) ∧
              List.Mem (gapFailureBridgeAuditEncodeBHist F)
                (gapFailureBridgeAuditToEventFlow
                  (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) ∧
              Cont gapFailure bridgeAxis auditRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro gapRoute bridgeRoute auditRoute auditPkg
  have sourceAudit :
      (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg) auditRead := by
    exact ⟨hsame_refl auditRead, auditPkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
        (fun row : BHist =>
          hsame row T ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨ hsame row X ∨
            Cont T F gapFailure ∨ Cont B X bridgeAxis)
        (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead sourceAudit
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, auditPkg⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl gapRoute)))))
    ledger_sound := by
      intro _row source
      exact source
  }
  have tEncoded :
      List.Mem (gapFailureBridgeAuditEncodeBHist T)
        (gapFailureBridgeAuditToEventFlow
          (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) := by
    change
      List.Mem (gapFailureBridgeAuditEncodeBHist T)
        [[BMark.b0], gapFailureBridgeAuditEncodeBHist T, [BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist F, [BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist L,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist X,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist A,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          gapFailureBridgeAuditEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist N]
    exact List.Mem.tail _ (List.Mem.head _)
  have fEncoded :
      List.Mem (gapFailureBridgeAuditEncodeBHist F)
        (gapFailureBridgeAuditToEventFlow
          (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) := by
    change
      List.Mem (gapFailureBridgeAuditEncodeBHist F)
        [[BMark.b0], gapFailureBridgeAuditEncodeBHist T, [BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist F, [BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist L,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist X,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist A,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          gapFailureBridgeAuditEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist N]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  exact ⟨cert, tEncoded, fEncoded, auditRoute⟩

theorem GapFailureBridgeAuditPacket_public_surface [AskSetup] [PackageSetup]
    {T F B L X A H C P N gapFailure bridgeAxis auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T F gapFailure →
      Cont B X bridgeAxis →
        Cont gapFailure bridgeAxis auditRead →
          PkgSig bundle auditRead pkg →
            FieldFaithful.fields (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
                [T, F, B, L, X, A, H, C, P, N] ∧
              List.Mem (gapFailureBridgeAuditEncodeBHist B)
                (gapFailureBridgeAuditToEventFlow
                  (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) ∧
                List.Mem (gapFailureBridgeAuditEncodeBHist X)
                  (gapFailureBridgeAuditToEventFlow
                    (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) ∧
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row auditRead ∧
                        FieldFaithful.fields
                            (GapFailureBridgeAuditUp.mk T F B L X A H C P N) =
                          [T, F, B, L, X, A, H, C, P, N])
                    (fun row : BHist =>
                      hsame row T ∨ hsame row F ∨ hsame row B ∨ hsame row L ∨
                        hsame row X ∨ Cont T F gapFailure ∨ Cont B X bridgeAxis)
                    (fun row : BHist => hsame row auditRead ∧ PkgSig bundle auditRead pkg)
                    hsame ∧
                    Cont B X bridgeAxis := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro gapRoute bridgeRoute auditRoute auditPkg
  have obligations :=
    GapFailureBridgeAuditPacket_namecert_obligations
      (T := T) (F := F) (B := B) (L := L) (X := X) (A := A) (H := H) (C := C)
      (P := P) (N := N) (gapFailure := gapFailure) (bridgeAxis := bridgeAxis)
      (auditRead := auditRead) (bundle := bundle) (pkg := pkg)
      gapRoute bridgeRoute auditRoute auditPkg
  have bEncoded :
      List.Mem (gapFailureBridgeAuditEncodeBHist B)
        (gapFailureBridgeAuditToEventFlow
          (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) := by
    change
      List.Mem (gapFailureBridgeAuditEncodeBHist B)
        [[BMark.b0], gapFailureBridgeAuditEncodeBHist T, [BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist F, [BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist L,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist X,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist A,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          gapFailureBridgeAuditEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist N]
    exact
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.head _)))))
  have xEncoded :
      List.Mem (gapFailureBridgeAuditEncodeBHist X)
        (gapFailureBridgeAuditToEventFlow
          (GapFailureBridgeAuditUp.mk T F B L X A H C P N)) := by
    change
      List.Mem (gapFailureBridgeAuditEncodeBHist X)
        [[BMark.b0], gapFailureBridgeAuditEncodeBHist T, [BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist F, [BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist L,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist X,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist A,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          gapFailureBridgeAuditEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          gapFailureBridgeAuditEncodeBHist N]
    exact
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))
  exact ⟨obligations.right.left, bEncoded, xEncoded, obligations.left, bridgeRoute⟩

end BEDC.Derived.GapFailureBridgeAuditUp
