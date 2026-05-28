import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RepresentedSpaceUp [AskSetup] [PackageSetup]
    (name schedule relation target transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig UnaryHistory
  UnaryHistory name ∧ UnaryHistory schedule ∧ UnaryHistory relation ∧
    UnaryHistory target ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont name schedule replay ∧
        Cont relation target transport ∧ hsame localName transport ∧
          PkgSig bundle provenance pkg

namespace RepresentedSpaceUp

theorem RepresentedSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row transport)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame ∧
        Cont name schedule replay ∧ Cont relation target transport ∧
          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWitness :
      BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg :=
    carrier
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, _targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, nameScheduleReplay,
    relationTargetTransport, localNameTransport, provenancePkg⟩ := carrier
  have sourceLocalName :
      (fun row : BHist =>
        BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
          provenance localName bundle pkg ∧ hsame row localName) localName := by
    exact ⟨carrierWitness, hsame_refl localName⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
              provenance localName bundle pkg ∧ hsame row localName)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row target ∨ hsame row transport)
          (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocalName
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (hsame_trans source.right localNameTransport))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }
  exact ⟨cert, nameScheduleReplay, relationTargetTransport, provenancePkg⟩

theorem RepresentedSpaceCarrier_representation_relation_exactness [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName relationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont relation target relationRead →
        PkgSig bundle relationRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row transport ∨ hsame row relationRead)
              (fun row : BHist =>
                hsame row relation ∨ hsame row target ∨ hsame row transport ∨
                  hsame row relationRead)
              (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle relationRead pkg)
              hsame ∧
            UnaryHistory relationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier relationReadRoute relationReadPkg
  obtain ⟨_nameUnary, _scheduleUnary, relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have relationReadUnary : UnaryHistory relationRead :=
    unary_cont_closed relationUnary targetUnary relationReadRoute
  have transportSameRelationRead : hsame transport relationRead :=
    cont_respects_hsame (hsame_refl relation) (hsame_refl target) relationTargetTransport
      relationReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transport ∨ hsame row relationRead)
          (fun row : BHist =>
            hsame row relation ∨ hsame row target ∨ hsame row transport ∨
              hsame row relationRead)
          (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle relationRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transport (Or.inl (hsame_refl transport))
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
        cases source with
        | inl sameTransport =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameTransport)
        | inr sameRelationRead =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameRelationRead)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameTransport =>
          exact Or.inr (Or.inr (Or.inl sameTransport))
      | inr sameRelationRead =>
          exact Or.inr (Or.inr (Or.inr sameRelationRead))
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, relationReadPkg⟩
  }
  have _relationReadTransportExact : hsame relationRead transport :=
    hsame_symm transportSameRelationRead
  exact ⟨cert, relationReadUnary⟩

theorem RepresentedSpaceCarrier_name_schedule_obligation [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      UnaryHistory name ∧ UnaryHistory schedule ∧ Cont name schedule replay ∧
        SemanticNameCert
          (fun row : BHist => hsame row schedule ∧ UnaryHistory row)
          (fun row : BHist => hsame row name ∨ hsame row schedule ∨ hsame row replay)
          (fun row : BHist => hsame row schedule ∧ PkgSig bundle provenance pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨nameUnary, scheduleUnary, _relationUnary, _targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have sourceSchedule :
      (fun row : BHist => hsame row schedule ∧ UnaryHistory row) schedule := by
    exact ⟨hsame_refl schedule, scheduleUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row schedule ∧ UnaryHistory row)
          (fun row : BHist => hsame row name ∨ hsame row schedule ∨ hsame row replay)
          (fun row : BHist => hsame row schedule ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro schedule sourceSchedule
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
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact ⟨nameUnary, scheduleUnary, nameScheduleReplay, cert⟩

theorem RepresentedSpaceCarrier_target_handoff_nonescape [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont target localName targetRead →
        PkgSig bundle targetRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row target ∨ hsame row localName ∨ hsame row targetRead ∨
                  hsame row transport)
              (fun row : BHist =>
                hsame row targetRead ∧ PkgSig bundle targetRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory targetRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier targetLocalNameRead targetReadPkg
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalNameRead
  have sourceTargetRead :
      (fun row : BHist => hsame row targetRead ∧ UnaryHistory row) targetRead := by
    exact ⟨hsame_refl targetRead, targetReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row target ∨ hsame row localName ∨ hsame row targetRead ∨
              hsame row transport)
          (fun row : BHist =>
            hsame row targetRead ∧ PkgSig bundle targetRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead sourceTargetRead
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, targetReadPkg, provenancePkg⟩
  }
  exact ⟨cert, targetReadUnary, provenancePkg⟩

theorem RepresentedSpaceCarrier_streamname_real_handoff [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName streamRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont name schedule streamRead →
        Cont target localName targetRead →
          PkgSig bundle streamRead pkg →
            PkgSig bundle targetRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row streamRead ∨ hsame row targetRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row name ∨ hsame row schedule ∨ hsame row target ∨
                      hsame row localName ∨ hsame row streamRead ∨ hsame row targetRead)
                  (fun row : BHist =>
                    (hsame row streamRead ∨ hsame row targetRead) ∧
                      PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory streamRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameScheduleStream targetLocalNameRead streamReadPkg targetReadPkg
  obtain ⟨nameUnary, scheduleUnary, _relationUnary, targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleStream
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed targetUnary localNameUnary targetLocalNameRead
  have sourceStreamRead :
      (fun row : BHist =>
        (hsame row streamRead ∨ hsame row targetRead) ∧ UnaryHistory row) streamRead := by
    exact ⟨Or.inl (hsame_refl streamRead), streamReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row streamRead ∨ hsame row targetRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row target ∨
              hsame row localName ∨ hsame row streamRead ∨ hsame row targetRead)
          (fun row : BHist =>
            (hsame row streamRead ∨ hsame row targetRead) ∧
              PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro streamRead sourceStreamRead
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
        cases source.left with
        | inl sameStream =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameStream),
                unary_transport source.right sameRows⟩
        | inr sameTarget =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameTarget),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameStream =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream))))
      | inr sameTarget =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameTarget))))
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameStream =>
          cases sameStream
          exact ⟨Or.inl (hsame_refl streamRead), streamReadPkg, provenancePkg⟩
      | inr sameTarget =>
          cases sameTarget
          exact ⟨Or.inr (hsame_refl targetRead), targetReadPkg, provenancePkg⟩
  }
  exact ⟨cert, streamReadUnary, targetReadUnary⟩

theorem RepresentedSpaceCarrier_schedule_representation_exactness [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName scheduledRead relationRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont name schedule scheduledRead →
        Cont scheduledRead relation relationRead →
          PkgSig bundle scheduledRead pkg →
            PkgSig bundle relationRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row scheduledRead ∨ hsame row relationRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
                      hsame row scheduledRead ∨ hsame row relationRead)
                  (fun row : BHist =>
                    (hsame row scheduledRead ∨ hsame row relationRead) ∧
                      PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory scheduledRead ∧ UnaryHistory relationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameScheduleRead scheduleRelationRead scheduledReadPkg relationReadPkg
  obtain ⟨nameUnary, scheduleUnary, relationUnary, _targetUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have scheduledReadUnary : UnaryHistory scheduledRead :=
    unary_cont_closed nameUnary scheduleUnary nameScheduleRead
  have relationReadUnary : UnaryHistory relationRead :=
    unary_cont_closed scheduledReadUnary relationUnary scheduleRelationRead
  have sourceScheduledRead :
      (fun row : BHist =>
        (hsame row scheduledRead ∨ hsame row relationRead) ∧ UnaryHistory row)
          scheduledRead := by
    exact ⟨Or.inl (hsame_refl scheduledRead), scheduledReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row scheduledRead ∨ hsame row relationRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨
              hsame row scheduledRead ∨ hsame row relationRead)
          (fun row : BHist =>
            (hsame row scheduledRead ∨ hsame row relationRead) ∧
              PkgSig bundle row pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scheduledRead sourceScheduledRead
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
        cases source.left with
        | inl sameScheduled =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameScheduled),
                unary_transport source.right sameRows⟩
        | inr sameRelation =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameRelation),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameScheduled =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameScheduled)))
      | inr sameRelation =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameRelation)))
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameScheduled =>
          cases sameScheduled
          exact ⟨Or.inl (hsame_refl scheduledRead), scheduledReadPkg, provenancePkg⟩
      | inr sameRelation =>
          cases sameRelation
          exact ⟨Or.inr (hsame_refl relationRead), relationReadPkg, provenancePkg⟩
  }
  exact ⟨cert, scheduledReadUnary, relationReadUnary⟩

theorem RepresentedSpaceCarrier_classifier_transport [AskSetup] [PackageSetup]
    {name schedule relation target transport replay provenance localName classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RepresentedSpaceUp name schedule relation target transport replay
        provenance localName bundle pkg →
      Cont transport replay classifierRead →
        PkgSig bundle classifierRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row name ∨ hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
                  hsame row transport ∨ hsame row replay ∨ hsame row classifierRead)
              (fun row : BHist =>
                hsame row classifierRead ∧ PkgSig bundle classifierRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory classifierRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier transportReplayRead classifierReadPkg
  obtain ⟨_nameUnary, _scheduleUnary, _relationUnary, _targetUnary, transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, _nameScheduleReplay,
    _relationTargetTransport, _localNameTransport, provenancePkg⟩ := carrier
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed transportUnary replayUnary transportReplayRead
  have sourceClassifierRead :
      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row) classifierRead := by
    exact ⟨hsame_refl classifierRead, classifierReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row name ∨ hsame row schedule ∨ hsame row relation ∨ hsame row target ∨
              hsame row transport ∨ hsame row replay ∨ hsame row classifierRead)
          (fun row : BHist =>
            hsame row classifierRead ∧ PkgSig bundle classifierRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceClassifierRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨hsame_refl classifierRead, classifierReadPkg, provenancePkg⟩
  }
  exact ⟨cert, classifierReadUnary, provenancePkg⟩

end RepresentedSpaceUp

end BEDC.Derived
