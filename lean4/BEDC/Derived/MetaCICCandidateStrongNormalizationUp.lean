import BEDC.Derived.MetaCICCandidateStrongNormalizationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICCandidateStrongNormalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

def MetaCICCandidateStrongNormalizationCarrier [AskSetup] [PackageSetup]
    (T K F E R A H C P N G : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory E ∧ UnaryHistory R ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      UnaryHistory G ∧
        FieldFaithful.fields (MetaCICCandidateStrongNormalizationUp.mk T K F E R A H C P N G) =
          [T, K, F, E, R, A, H, C, P, N, G] ∧
          Cont T K F ∧ Cont F E R ∧ Cont A H C ∧ PkgSig bundle P pkg ∧
            (forall {endpoint : BHist}, Cont C P endpoint -> PkgSig bundle endpoint pkg ->
              hsame endpoint K ∧ hsame endpoint E)

theorem MetaCICCandidateStrongNormalizationCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {T K F E R A H C P N G endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCandidateStrongNormalizationCarrier T K F E R A H C P N G bundle pkg ->
      Cont C P endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              MetaCICCandidateStrongNormalizationCarrier T K F E R A H C P N G bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist => hsame row K ∧ hsame row E)
            (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier replay endpointPkg
  have carrierPacket :
      MetaCICCandidateStrongNormalizationCarrier T K F E R A H C P N G bundle pkg :=
    carrier
  obtain ⟨_termUnary, _candidateUnary, _fuelUnary, _endpointUnary, _refusalUnary,
    _auditUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _tasteGateUnary, _fields, _termCandidateFuel, _fuelEndpointRefusal,
    _auditTransportReplay, _provenancePkg, endpointRows⟩ := carrier
  have endpointPattern : hsame endpoint K ∧ hsame endpoint E :=
    endpointRows replay endpointPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨carrierPacket, hsame_refl endpoint⟩
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
      exact
        ⟨hsame_trans source.right endpointPattern.left,
          hsame_trans source.right endpointPattern.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }

end BEDC.Derived.MetaCICCandidateStrongNormalizationUp
