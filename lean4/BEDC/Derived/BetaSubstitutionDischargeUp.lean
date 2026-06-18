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

end BEDC.Derived.BetaSubstitutionDischargeUp
