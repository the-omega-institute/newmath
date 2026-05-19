import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.AxisZeckendorfCarryBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisZeckendorfCarryBudgetCarrier [AskSetup] [PackageSetup]
    (source target carry normal value boundary transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory carry ∧
    UnaryHistory normal ∧ UnaryHistory value ∧ UnaryHistory boundary ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont source target carry ∧ Cont carry normal value ∧
          Cont value boundary transport ∧ Cont transport route provenance ∧
            PkgSig bundle name pkg

theorem AxisZeckendorfCarryBudgetNamecertObligations [AskSetup] [PackageSetup]
    {source target carry normal value boundary transport route provenance name valueRead
      boundaryRead certRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport route
        provenance name bundle pkg ->
      Cont source target carry ->
        Cont carry normal valueRead ->
          Cont value boundary boundaryRead ->
            Cont route name certRead ->
              PkgSig bundle certRead pkg ->
                SemanticNameCert
                  (fun row : BHist =>
                    AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary
                        transport route provenance name bundle pkg ∧
                      (hsame row valueRead ∨ hsame row boundaryRead ∨ hsame row certRead))
                  (fun _row : BHist =>
                    Cont carry normal valueRead ∧ Cont value boundary boundaryRead ∧
                      Cont route name certRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle certRead pkg)
                  hsame ∧
                  UnaryHistory valueRead ∧ UnaryHistory boundaryRead ∧
                    UnaryHistory certRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrierWitness _sourceTargetCarry carryNormalValueRead valueBoundaryRead routeNameCertRead
    certPkg
  have carrierInhabited :
      Exists
        (fun row : BHist =>
          AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport
              route provenance name bundle pkg ∧
            (hsame row valueRead ∨ hsame row boundaryRead ∨ hsame row certRead)) :=
    Exists.intro certRead ⟨carrierWitness, Or.inr (Or.inr (hsame_refl certRead))⟩
  obtain ⟨sourceUnary, targetUnary, carryUnary, normalUnary, valueUnary, boundaryUnary,
    _transportUnary, routeUnary, _provenanceUnary, nameUnary, _sourceTargetCarryCarrier,
    _carryNormalValue, _valueBoundaryTransport, _transportRouteProvenance, _namePkg⟩ :=
      carrierWitness
  have valueReadUnary : UnaryHistory valueRead :=
    unary_cont_closed carryUnary normalUnary carryNormalValueRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed valueUnary boundaryUnary valueBoundaryRead
  have certReadUnary : UnaryHistory certRead :=
    unary_cont_closed routeUnary nameUnary routeNameCertRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport
              route provenance name bundle pkg ∧
            (hsame row valueRead ∨ hsame row boundaryRead ∨ hsame row certRead))
        (fun _row : BHist =>
          Cont carry normal valueRead ∧ Cont value boundary boundaryRead ∧
            Cont route name certRead)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle certRead pkg)
        hsame := {
    core := {
      carrier_inhabited := carrierInhabited
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
        intro row other sameRows source
        cases source with
        | intro carrierSource sourceRead =>
            refine ⟨carrierSource, ?_⟩
            cases sourceRead with
            | inl sameValue =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameValue)
            | inr rest =>
                cases rest with
                | inl sameBoundary =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary))
                | inr sameCert =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameCert))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨carryNormalValueRead, valueBoundaryRead, routeNameCertRead⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _carrierSource sourceRead =>
          cases sourceRead with
          | inl sameValue =>
              exact ⟨unary_transport valueReadUnary (hsame_symm sameValue), certPkg⟩
          | inr rest =>
              cases rest with
              | inl sameBoundary =>
                  exact ⟨unary_transport boundaryReadUnary (hsame_symm sameBoundary), certPkg⟩
              | inr sameCert =>
                  exact ⟨unary_transport certReadUnary (hsame_symm sameCert), certPkg⟩
  }
  exact ⟨cert, valueReadUnary, boundaryReadUnary, certReadUnary⟩

theorem AxisZeckendorfCarryBudget_classifier_realization [AskSetup] [PackageSetup]
    {source target carry normal value boundary transport route provenance name carryRead
      budgetRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport route
        provenance name bundle pkg ->
      Cont source target carryRead ->
        Cont carryRead normal budgetRead ->
          Cont budgetRead boundary boundaryRead ->
            PkgSig bundle boundaryRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary
                        transport route provenance name bundle pkg ∧
                      (hsame row carryRead ∨ hsame row budgetRead ∨ hsame row boundaryRead))
                  (fun _row : BHist =>
                    Cont source target carryRead ∧ Cont carryRead normal budgetRead ∧
                      Cont budgetRead boundary boundaryRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory carryRead ∧ UnaryHistory budgetRead ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrierWitness sourceTargetCarryRead carryReadNormalBudgetRead
    budgetReadBoundaryRead boundaryPkg
  have carrierSource := carrierWitness
  obtain ⟨sourceUnary, targetUnary, _carryUnary, normalUnary, _valueUnary, boundaryUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _sourceTargetCarryCarrier,
    _carryNormalValue, _valueBoundaryTransport, _transportRouteProvenance, _namePkg⟩ :=
      carrierWitness
  have carryReadUnary : UnaryHistory carryRead :=
    unary_cont_closed sourceUnary targetUnary sourceTargetCarryRead
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed carryReadUnary normalUnary carryReadNormalBudgetRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed budgetReadUnary boundaryUnary budgetReadBoundaryRead
  have carrierInhabited :
      Exists
        (fun row : BHist =>
          AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport
              route provenance name bundle pkg ∧
            (hsame row carryRead ∨ hsame row budgetRead ∨ hsame row boundaryRead)) :=
    Exists.intro boundaryRead ⟨carrierSource, Or.inr (Or.inr (hsame_refl boundaryRead))⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          AxisZeckendorfCarryBudgetCarrier source target carry normal value boundary transport
              route provenance name bundle pkg ∧
            (hsame row carryRead ∨ hsame row budgetRead ∨ hsame row boundaryRead))
        (fun _row : BHist =>
          Cont source target carryRead ∧ Cont carryRead normal budgetRead ∧
            Cont budgetRead boundary boundaryRead)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundaryRead pkg)
        hsame := {
    core := {
      carrier_inhabited := carrierInhabited
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
        intro row other sameRows source
        cases source with
        | intro carrierSource sourceRead =>
            refine ⟨carrierSource, ?_⟩
            cases sourceRead with
            | inl sameCarry =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameCarry)
            | inr rest =>
                cases rest with
                | inl sameBudget =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBudget))
                | inr sameBoundary =>
                    exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameBoundary))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨sourceTargetCarryRead, carryReadNormalBudgetRead, budgetReadBoundaryRead⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _carrierSource sourceRead =>
          cases sourceRead with
          | inl sameCarry =>
              exact ⟨unary_transport carryReadUnary (hsame_symm sameCarry), boundaryPkg⟩
          | inr rest =>
              cases rest with
              | inl sameBudget =>
                  exact ⟨unary_transport budgetReadUnary (hsame_symm sameBudget), boundaryPkg⟩
              | inr sameBoundary =>
                  exact
                    ⟨unary_transport boundaryReadUnary (hsame_symm sameBoundary),
                      boundaryPkg⟩
  }
  exact ⟨cert, carryReadUnary, budgetReadUnary, boundaryReadUnary⟩

end BEDC.Derived.AxisZeckendorfCarryBudgetUp
