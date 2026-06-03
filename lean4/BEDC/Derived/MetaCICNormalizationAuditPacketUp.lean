import BEDC.Derived.MetaCICNormalizationAuditPacketUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICNormalizationAuditPacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

def MetaCICNormalizationAuditPacketCarrier [AskSetup] [PackageSetup]
    (T K A S I P F H C G N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory T ∧ UnaryHistory K ∧ UnaryHistory A ∧ UnaryHistory S ∧ UnaryHistory I ∧
    UnaryHistory P ∧ UnaryHistory F ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory G ∧
      UnaryHistory N ∧
        FieldFaithful.fields (MetaCICNormalizationAuditPacketUp.mk T K A S I P F H C G N) =
          [T, K, A, S, I, P, F, H, C, G, N] ∧
          Cont T K A ∧ Cont S I P ∧ Cont F H C ∧ PkgSig bundle G pkg ∧
            (forall {endpoint : BHist}, Cont C N endpoint -> PkgSig bundle endpoint pkg ->
              hsame endpoint S ∧ hsame endpoint I)

theorem MetaCICNormalizationAuditPacketCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {T K A S I P F H C G N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICNormalizationAuditPacketCarrier T K A S I P F H C G N bundle pkg ->
      Cont C N endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              MetaCICNormalizationAuditPacketCarrier T K A S I P F H C G N bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist => hsame row S ∧ hsame row I)
            (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier replay endpointPkg
  have carrierPacket :
      MetaCICNormalizationAuditPacketCarrier T K A S I P F H C G N bundle pkg :=
    carrier
  obtain ⟨_termUnary, _candidateUnary, _appUnary, _snUnary, _noInfUnary, _piUnary,
    _frontierUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _fields, _termCandidateRoute, _snNoInfiniteRoute, _frontierTransportRoute,
    _provenancePkg, endpointRows⟩ := carrier
  have endpointPattern : hsame endpoint S ∧ hsame endpoint I :=
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

end BEDC.Derived.MetaCICNormalizationAuditPacketUp
