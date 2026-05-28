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

end RepresentedSpaceUp

end BEDC.Derived
