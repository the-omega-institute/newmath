import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubstitutionContextAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubstitutionContextAuditCarrier [AskSetup] [PackageSetup]
    (context shift subst composition generator binder handoff transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  UnaryHistory context ∧ UnaryHistory shift ∧ UnaryHistory subst ∧
    UnaryHistory composition ∧ UnaryHistory generator ∧ UnaryHistory binder ∧
      UnaryHistory handoff ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧ Cont context shift subst ∧
          Cont subst composition generator ∧ Cont binder handoff replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem SubstitutionContextAuditNameCertObligation [AskSetup] [PackageSetup]
    {context shift subst composition generator binder handoff transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionContextAuditCarrier context shift subst composition generator binder handoff
      transport replay provenance name bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row context ∨ hsame row shift ∨ hsame row subst ∨
              hsame row composition ∨ hsame row generator ∨ hsame row binder ∨
                hsame row handoff ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont context shift subst ∧
              Cont subst composition generator ∧ Cont binder handoff replay ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame ∧ UnaryHistory subst ∧ UnaryHistory generator ∧ UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_contextUnary, _shiftUnary, substUnary, _compositionUnary, generatorUnary,
    _binderUnary, _handoffUnary, _transportUnary, replayUnary, _provenanceUnary,
    nameUnary, substRoute, generatorRoute, replayRoute, provenancePkg, namePkg⟩ :=
    carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row context ∨ hsame row shift ∨ hsame row subst ∨
              hsame row composition ∨ hsame row generator ∨ hsame row binder ∨
                hsame row handoff ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont context shift subst ∧
              Cont subst composition generator ∧ Cont binder handoff replay ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, substRoute, generatorRoute, replayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, substUnary, generatorUnary, replayUnary⟩

theorem SubstitutionContextAuditBinderRoute [AskSetup] [PackageSetup]
    {context shift subst composition generator binder handoff transport replay provenance
      name binderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubstitutionContextAuditCarrier context shift subst composition generator binder handoff
      transport replay provenance name bundle pkg →
      Cont context binder binderRead →
        PkgSig bundle binderRead pkg →
          UnaryHistory context ∧ UnaryHistory shift ∧ UnaryHistory subst ∧
            UnaryHistory composition ∧ UnaryHistory generator ∧ UnaryHistory binder ∧
              UnaryHistory binderRead ∧ Cont context shift subst ∧
                Cont subst composition generator ∧ Cont binder handoff replay ∧
                  Cont context binder binderRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle binderRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier binderRoute binderPkg
  obtain ⟨contextUnary, shiftUnary, substUnary, compositionUnary, generatorUnary,
    binderUnary, _handoffUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, substRoute, generatorRoute, replayRoute, provenancePkg, namePkg⟩ :=
    carrier
  have binderReadUnary : UnaryHistory binderRead :=
    unary_cont_closed contextUnary binderUnary binderRoute
  exact
    ⟨contextUnary, shiftUnary, substUnary, compositionUnary, generatorUnary, binderUnary,
      binderReadUnary, substRoute, generatorRoute, replayRoute, binderRoute, provenancePkg,
      namePkg, binderPkg⟩

end BEDC.Derived.SubstitutionContextAuditUp
