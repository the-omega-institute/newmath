import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirichletUniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DirichletUniformModulusCarrier [AskSetup] [PackageSetup]
    (boundedSums abelWindow monotoneWindow dyadicBudget modulusRow transports replay
      provenance localNameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory boundedSums ∧ UnaryHistory abelWindow ∧ UnaryHistory monotoneWindow ∧
    UnaryHistory dyadicBudget ∧ UnaryHistory modulusRow ∧ UnaryHistory transports ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localNameCert ∧
        Cont boundedSums abelWindow monotoneWindow ∧
          Cont monotoneWindow dyadicBudget modulusRow ∧
            Cont modulusRow replay provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg

theorem DirichletUniformModulusPacket_semantic_name_certificate_modulus_consumer
    [AskSetup] [PackageSetup]
    {boundedSums abelWindow monotoneWindow dyadicBudget modulusRow transports replay
      provenance localNameCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirichletUniformModulusCarrier boundedSums abelWindow monotoneWindow dyadicBudget
        modulusRow transports replay provenance localNameCert bundle pkg ->
      Cont modulusRow replay consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row modulusRow ∨ hsame row consumerRead)
              (fun row : BHist => hsame row modulusRow ∨ hsame row consumerRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg ∧
                  PkgSig bundle consumerRead pkg ∧
                    (hsame row modulusRow ∨ hsame row consumerRead))
              hsame ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modulusReplayConsumer consumerPkg
  obtain ⟨_boundedUnary, _abelUnary, _monotoneUnary, _dyadicUnary, modulusUnary,
    _transportsUnary, replayUnary, _provenanceUnary, _localNameCertUnary,
    _boundedAbelMonotone, _monotoneDyadicModulus, _modulusReplayProvenance,
    provenancePkg, localNameCertPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed modulusUnary replayUnary modulusReplayConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRow ∨ hsame row consumerRead)
          (fun row : BHist => hsame row modulusRow ∨ hsame row consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localNameCert pkg ∧
              PkgSig bundle consumerRead pkg ∧
                (hsame row modulusRow ∨ hsame row consumerRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRow (Or.inl (hsame_refl modulusRow))
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
        | inl sameModulus =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameModulus)
        | inr sameConsumer =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameConsumer)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNameCertPkg, consumerPkg, source⟩
  }
  exact ⟨cert, consumerUnary⟩

theorem DirichletUniformModulusTailBudget [AskSetup] [PackageSetup]
    {boundedSums abelWindow monotoneWindow dyadicBudget modulusRow transports replay
      provenance localNameCert tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirichletUniformModulusCarrier boundedSums abelWindow monotoneWindow dyadicBudget
        modulusRow transports replay provenance localNameCert bundle pkg ->
      Cont monotoneWindow dyadicBudget tailRead ->
        PkgSig bundle tailRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row monotoneWindow ∨ hsame row dyadicBudget ∨
                  hsame row modulusRow ∨ hsame row tailRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localNameCert pkg ∧ PkgSig bundle tailRead pkg)
              hsame ∧ UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier monotoneDyadicTail tailPkg
  obtain ⟨_boundedUnary, _abelUnary, monotoneUnary, dyadicUnary, _modulusUnary,
    _transportsUnary, _replayUnary, _provenanceUnary, _localNameCertUnary,
    _boundedAbelMonotone, _monotoneDyadicModulus, _modulusReplayProvenance,
    provenancePkg, localNameCertPkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed monotoneUnary dyadicUnary monotoneDyadicTail
  have sourceTail :
      (fun row : BHist => hsame row tailRead ∧ UnaryHistory row) tailRead := by
    exact ⟨hsame_refl tailRead, tailUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row monotoneWindow ∨ hsame row dyadicBudget ∨ hsame row modulusRow ∨
              hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localNameCert pkg ∧ PkgSig bundle tailRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead sourceTail
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNameCertPkg, tailPkg⟩
  }
  exact ⟨cert, tailUnary⟩

end BEDC.Derived.DirichletUniformModulusUp
