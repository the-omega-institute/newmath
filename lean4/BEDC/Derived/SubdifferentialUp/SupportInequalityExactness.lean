import BEDC.Derived.SubdifferentialUp.TasteGate

namespace BEDC.Derived.SubdifferentialUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubdifferentialSupportInequalityExactness [AskSetup] [PackageSetup]
    {functional point covector pairing support epigraph cone transport replay provenance name
      supportRead stationarityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubdifferentialCarrier functional point covector pairing support epigraph cone transport
        replay provenance name bundle pkg →
      Cont pairing support supportRead →
        Cont support cone stationarityRead →
          UnaryHistory supportRead ∧ Cont pairing support supportRead ∧
            UnaryHistory stationarityRead ∧ Cont support cone stationarityRead ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier supportRoute stationarityRoute
  obtain ⟨_functionalUnary, _pointUnary, _covectorUnary, pairingUnary, supportUnary,
    _epigraphUnary, coneUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _epigraphRoute, _replayRoute, provenancePkg⟩ := carrier
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed pairingUnary supportUnary supportRoute
  have stationarityReadUnary : UnaryHistory stationarityRead :=
    unary_cont_closed supportUnary coneUnary stationarityRoute
  exact
    ⟨supportReadUnary, supportRoute, stationarityReadUnary, stationarityRoute, provenancePkg⟩

theorem SubdifferentialSupportNameCert_consumer [AskSetup] [PackageSetup]
    {functional point covector pairing support epigraph cone transport replay provenance name
      supportRead stationarityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubdifferentialCarrier functional point covector pairing support epigraph cone transport
        replay provenance name bundle pkg →
      Cont pairing support supportRead →
        Cont support cone stationarityRead →
          SemanticNameCert
              (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row functional ∨ hsame row point ∨ hsame row covector ∨
                  hsame row pairing ∨ hsame row support ∨ hsame row epigraph ∨
                    hsame row cone ∨ hsame row supportRead ∨ hsame row stationarityRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont pairing support supportRead ∧
                  Cont support cone stationarityRead ∧ PkgSig bundle provenance pkg)
              hsame ∧ UnaryHistory supportRead ∧ UnaryHistory stationarityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier supportRoute stationarityRoute
  have obligations :=
    BEDC.Derived.SubdifferentialUp.SubdifferentialCarrier_namecert_obligations
      carrier supportRoute stationarityRoute
  obtain ⟨_functionalUnary, _pointUnary, _covectorUnary, _pairingUnary, supportUnary,
    _epigraphUnary, _coneUnary, supportReadUnary, stationarityReadUnary, _supportRoute,
    _stationarityRoute, provenancePkg⟩ := obligations
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row supportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row functional ∨ hsame row point ∨ hsame row covector ∨
              hsame row pairing ∨ hsame row support ∨ hsame row epigraph ∨
                hsame row cone ∨ hsame row supportRead ∨ hsame row stationarityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont pairing support supportRead ∧
              Cont support cone stationarityRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro supportRead ⟨hsame_refl supportRead, supportReadUnary⟩
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
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, supportRoute, stationarityRoute, provenancePkg⟩
  }
  exact ⟨cert, supportReadUnary, stationarityReadUnary⟩

end BEDC.Derived.SubdifferentialUp
