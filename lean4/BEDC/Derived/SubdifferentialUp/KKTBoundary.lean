import BEDC.Derived.SubdifferentialUp.TasteGate

namespace BEDC.Derived.SubdifferentialUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubdifferentialCarrier_kkt_boundary [AskSetup] [PackageSetup]
    {functional point covector pairing support epigraph cone transport replay provenance name
      supportRead stationarityRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubdifferentialCarrier functional point covector pairing support epigraph cone transport
        replay provenance name bundle pkg →
      Cont pairing support supportRead →
        Cont support cone stationarityRead →
          Cont stationarityRead provenance namedRead →
            PkgSig bundle name pkg →
              SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row functional ∨ hsame row point ∨ hsame row covector ∨
                    hsame row pairing ∨ hsame row support ∨ hsame row epigraph ∨
                      hsame row cone ∨ hsame row transport ∨ hsame row replay ∨
                        hsame row provenance ∨ hsame row name ∨ hsame row supportRead ∨
                          hsame row stationarityRead ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont pairing support supportRead ∧
                    Cont support cone stationarityRead ∧
                      Cont stationarityRead provenance namedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
                hsame ∧ UnaryHistory supportRead ∧ UnaryHistory stationarityRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier supportRoute stationarityRoute namedRoute namePkg
  obtain ⟨_functionalUnary, _pointUnary, _covectorUnary, pairingUnary, supportUnary,
    _epigraphUnary, coneUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    _epigraphRoute, _replayRoute, provenancePkg⟩ := carrier
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed pairingUnary supportUnary supportRoute
  have stationarityReadUnary : UnaryHistory stationarityRead :=
    unary_cont_closed supportUnary coneUnary stationarityRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed stationarityReadUnary provenanceUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row functional ∨ hsame row point ∨ hsame row covector ∨
            hsame row pairing ∨ hsame row support ∨ hsame row epigraph ∨
              hsame row cone ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row name ∨ hsame row supportRead ∨
                  hsame row stationarityRead ∨ hsame row namedRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont pairing support supportRead ∧
            Cont support cone stationarityRead ∧ Cont stationarityRead provenance namedRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, supportRoute, stationarityRoute, namedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, supportReadUnary, stationarityReadUnary, namedReadUnary⟩

end BEDC.Derived.SubdifferentialUp
