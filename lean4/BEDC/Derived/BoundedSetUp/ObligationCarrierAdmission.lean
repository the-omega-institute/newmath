import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_obligation_carrier_admission [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow admittedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont nameRow provenance admittedRead ->
        PkgSig bundle admittedRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row admittedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
                  hsame row ball ∨ hsame row nameRow ∨ Cont nameRow provenance admittedRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle admittedRead pkg ∧
                  hsame row admittedRead)
              hsame ∧
            UnaryHistory X ∧ UnaryHistory S ∧ UnaryHistory center ∧ UnaryHistory radius ∧
              UnaryHistory ball ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
                UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory admittedRead ∧
                  Cont nameRow provenance admittedRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle admittedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier nameAdmission admittedPkg
  obtain ⟨xUnary, sUnary, centerUnary, radiusUnary, ballUnary, transportUnary, replayUnary,
    provenanceUnary, nameUnary, _carrierMemberRoute, _carrierBallRoute, provenancePkg,
    _namePkg⟩ := carrier
  have admittedUnary : UnaryHistory admittedRead :=
    unary_cont_closed nameUnary provenanceUnary nameAdmission
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row admittedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row center ∨ hsame row radius ∨
              hsame row ball ∨ hsame row nameRow ∨ Cont nameRow provenance admittedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle admittedRead pkg ∧
              hsame row admittedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro admittedRead
        ⟨hsame_refl admittedRead, admittedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr nameAdmission)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, admittedPkg, source.left⟩
  }
  exact
    ⟨cert, xUnary, sUnary, centerUnary, radiusUnary, ballUnary, transportUnary,
      replayUnary, provenanceUnary, nameUnary, admittedUnary, nameAdmission, provenancePkg,
      admittedPkg⟩

end BEDC.Derived.BoundedSetUp
