import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BetaSubstitutionDischargeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BetaSubstitutionDischargeCarrier [AskSetup] [PackageSetup]
    (context domain body argument codomain subst transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory context ∧ UnaryHistory domain ∧ UnaryHistory body ∧
    UnaryHistory argument ∧ UnaryHistory codomain ∧ UnaryHistory subst ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont body argument subst ∧ Cont subst transport replay ∧
          PkgSig bundle provenance pkg

theorem BetaSubstitutionDischarge_namecert_obligations [AskSetup] [PackageSetup]
    {context domain body argument codomain subst transport replay provenance localName
      betaRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BetaSubstitutionDischargeCarrier context domain body argument codomain subst transport
        replay provenance localName bundle pkg →
      Cont subst replay betaRead →
        PkgSig bundle betaRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row betaRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row context ∨ hsame row domain ∨ hsame row body ∨
                  hsame row argument ∨ hsame row codomain ∨ hsame row subst ∨
                    hsame row betaRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont subst replay betaRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle betaRead pkg)
              hsame ∧
            UnaryHistory betaRead := by
  -- BEDC touchpoint anchor: BetaSubstitutionDischargeCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier substReplayBeta betaPkg
  obtain ⟨_contextUnary, _domainUnary, _bodyUnary, _argumentUnary, _codomainUnary,
    substUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _bodyArgumentSubst, _substTransportReplay, provenancePkg⟩ := carrier
  have betaUnary : UnaryHistory betaRead :=
    unary_cont_closed substUnary replayUnary substReplayBeta
  have sourceBeta :
      (fun row : BHist => hsame row betaRead ∧ UnaryHistory row) betaRead := by
    exact ⟨hsame_refl betaRead, betaUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row betaRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row context ∨ hsame row domain ∨ hsame row body ∨
              hsame row argument ∨ hsame row codomain ∨ hsame row subst ∨
                hsame row betaRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont subst replay betaRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle betaRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro betaRead sourceBeta
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
      exact ⟨source.right, substReplayBeta, provenancePkg, betaPkg⟩
  }
  exact ⟨cert, betaUnary⟩

theorem BetaSubstitutionDischargeCarrier_binder_boundary [AskSetup] [PackageSetup]
    {context domain body argument codomain subst transport replay provenance localName
      binderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BetaSubstitutionDischargeCarrier context domain body argument codomain subst transport
        replay provenance localName bundle pkg →
      Cont subst replay binderRead →
        UnaryHistory context ∧ UnaryHistory domain ∧ UnaryHistory body ∧
          UnaryHistory argument ∧ UnaryHistory codomain ∧ UnaryHistory subst ∧
            UnaryHistory binderRead ∧ Cont body argument subst ∧
              Cont subst replay binderRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BetaSubstitutionDischargeCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier substReplayBinder
  obtain ⟨contextUnary, domainUnary, bodyUnary, argumentUnary, codomainUnary, substUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localNameUnary, bodyArgumentSubst,
    _substTransportReplay, provenancePkg⟩ := carrier
  have binderUnary : UnaryHistory binderRead :=
    unary_cont_closed substUnary replayUnary substReplayBinder
  exact
    ⟨contextUnary, domainUnary, bodyUnary, argumentUnary, codomainUnary, substUnary,
      binderUnary, bodyArgumentSubst, substReplayBinder, provenancePkg⟩

theorem BetaSubstitutionDischargeCarrier_component_transport [AskSetup] [PackageSetup]
    {context domain body argument codomain subst transport replay provenance localName
      transportedSubst transportedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BetaSubstitutionDischargeCarrier context domain body argument codomain subst transport
        replay provenance localName bundle pkg →
      hsame subst transportedSubst →
        hsame replay transportedReplay →
          UnaryHistory transportedSubst ∧ UnaryHistory transportedReplay ∧
            PkgSig bundle provenance pkg ∧ hsame transportedSubst subst ∧
              hsame transportedReplay replay := by
  -- BEDC touchpoint anchor: BetaSubstitutionDischargeCarrier BHist hsame UnaryHistory PkgSig
  intro carrier substSame replaySame
  obtain ⟨_contextUnary, _domainUnary, _bodyUnary, _argumentUnary, _codomainUnary,
    substUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _bodyArgumentSubst, _substTransportReplay, provenancePkg⟩ := carrier
  exact
    ⟨unary_transport substUnary substSame,
      unary_transport replayUnary replaySame,
      provenancePkg,
      hsame_symm substSame,
      hsame_symm replaySame⟩

theorem BetaSubstitutionDischargeCarrier_replay_exactness [AskSetup] [PackageSetup]
    {context domain body argument codomain subst transport replay provenance localName
      bodyRead codomainRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BetaSubstitutionDischargeCarrier context domain body argument codomain subst transport
        replay provenance localName bundle pkg →
      Cont body subst bodyRead →
        Cont codomain subst codomainRead →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row bodyRead ∨ hsame row codomainRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row context ∨ hsame row domain ∨ hsame row body ∨
                  hsame row argument ∨ hsame row codomain ∨ hsame row subst ∨
                    hsame row replay ∨ hsame row bodyRead ∨ hsame row codomainRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont body subst bodyRead ∧
                  Cont codomain subst codomainRead ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory bodyRead ∧ UnaryHistory codomainRead := by
  -- BEDC touchpoint anchor: BetaSubstitutionDischargeCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier bodySubst codomainSubst
  obtain ⟨_contextUnary, _domainUnary, bodyUnary, _argumentUnary, codomainUnary,
    substUnary, _transportUnary, replayUnary, provenanceUnary, _localNameUnary,
    _bodyArgumentSubst, _substTransportReplay, provenancePkg⟩ := carrier
  have bodyReadUnary : UnaryHistory bodyRead :=
    unary_cont_closed bodyUnary substUnary bodySubst
  have codomainReadUnary : UnaryHistory codomainRead :=
    unary_cont_closed codomainUnary substUnary codomainSubst
  have sourceBody :
      (fun row : BHist =>
        (hsame row bodyRead ∨ hsame row codomainRead) ∧ UnaryHistory row) bodyRead := by
    exact ⟨Or.inl (hsame_refl bodyRead), bodyReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row bodyRead ∨ hsame row codomainRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row context ∨ hsame row domain ∨ hsame row body ∨
              hsame row argument ∨ hsame row codomain ∨ hsame row subst ∨
                hsame row replay ∨ hsame row bodyRead ∨ hsame row codomainRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont body subst bodyRead ∧
              Cont codomain subst codomainRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bodyRead sourceBody
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
          ⟨Or.elim source.left
              (fun sameBody =>
                Or.inl (hsame_trans (hsame_symm sameRows) sameBody))
              (fun sameCodomain =>
                Or.inr (hsame_trans (hsame_symm sameRows) sameCodomain)),
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameBody =>
          right; right; right; right; right; right; right; left
          exact sameBody
      | inr sameCodomain =>
          right; right; right; right; right; right; right; right
          exact sameCodomain
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bodySubst, codomainSubst, provenancePkg⟩
  }
  exact ⟨cert, bodyReadUnary, codomainReadUnary⟩

end BEDC.Derived.BetaSubstitutionDischargeUp
