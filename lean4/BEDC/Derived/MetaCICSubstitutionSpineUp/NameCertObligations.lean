import BEDC.Derived.MetaCICSubstitutionSpineUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICSubstitutionSpineUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

def MetaCICSubstitutionSpineCarrier [AskSetup] [PackageSetup]
    (T V D Q R L A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory T ∧ UnaryHistory V ∧ UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory R ∧
    UnaryHistory L ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧
        FieldFaithful.fields (MetaCICSubstitutionSpineUp.mk T V D Q R L A H C P N) =
          [T, V, D, Q, R, L, A, H, C, P, N] ∧
          Cont T V D ∧ Cont Q R L ∧ Cont A H C ∧ PkgSig bundle P pkg ∧
            (forall {endpoint : BHist}, Cont C P endpoint -> PkgSig bundle endpoint pkg ->
              hsame endpoint R ∧ hsame endpoint L ∧ hsame endpoint A)

theorem MetaCICSubstitutionSpineCarrier_namecert_obligations
    [AskSetup] [PackageSetup]
    {T V D Q R L A H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICSubstitutionSpineCarrier T V D Q R L A H C P N bundle pkg ->
      Cont C P endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              MetaCICSubstitutionSpineCarrier T V D Q R L A H C P N bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist => hsame row R ∧ hsame row L ∧ hsame row A)
            (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier replay endpointPkg
  have carrierPacket :
      MetaCICSubstitutionSpineCarrier T V D Q R L A H C P N bundle pkg :=
    carrier
  obtain ⟨_termUnary, _variableUnary, _depthUnary, _closedUnary, _shiftUnary,
    _substUnary, _auditUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fields, _termVariableDepth, _closedShiftSubst, _auditTransportReplay,
    _provenancePkg, endpointRows⟩ := carrier
  have endpointPattern : hsame endpoint R ∧ hsame endpoint L ∧ hsame endpoint A :=
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
          hsame_trans source.right endpointPattern.right.left,
          hsame_trans source.right endpointPattern.right.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }

end BEDC.Derived.MetaCICSubstitutionSpineUp
