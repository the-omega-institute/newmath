import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_metric_bornology_consumer [AskSetup] [PackageSetup]
    {X S c r B H C P N bornology : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S c r B H C P N bundle pkg ->
      Cont B H bornology ->
        PkgSig bundle bornology pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row bornology ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row S ∨ hsame row c ∨ hsame row r ∨ hsame row B ∨
                  Cont B H bornology)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle bornology pkg ∧ hsame row bornology)
              hsame ∧
            UnaryHistory bornology ∧ Cont B H bornology ∧ PkgSig bundle P pkg ∧
              PkgSig bundle bornology pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier ballTransportBornology bornologyPkg
  obtain ⟨_xUnary, _sUnary, _centerUnary, _radiusUnary, ballUnary, transportUnary,
    _replayUnary, provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have bornologyUnary : UnaryHistory bornology :=
    unary_cont_closed ballUnary transportUnary ballTransportBornology
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bornology ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row c ∨ hsame row r ∨ hsame row B ∨
              Cont B H bornology)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle bornology pkg ∧ hsame row bornology)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bornology ⟨hsame_refl bornology, bornologyUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ballTransportBornology))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, bornologyPkg, source.left⟩
  }
  exact ⟨cert, bornologyUnary, ballTransportBornology, provenancePkg, bornologyPkg⟩

end BEDC.Derived.BoundedSetUp
