import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_bounded_sequence_admission [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceAdmission sourceSupport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K sourceAdmission ->
        Cont sourceAdmission H sourceSupport ->
          PkgSig bundle sourceSupport pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sourceSupport ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                    hsame row E ∨ hsame row sourceAdmission ∨ hsame row sourceSupport)
                (fun row : BHist =>
                  hsame row sourceSupport ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle sourceSupport pkg)
                hsame ∧
              UnaryHistory sourceAdmission ∧ UnaryHistory sourceSupport := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier admissionRoute supportRoute supportPkg
  obtain ⟨SUnary, KUnary, _RUnary, _QUnary, _EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceRoute, _readbackRoute, _clusterRoute, carrierPkg⟩ := carrier
  have admissionUnary : UnaryHistory sourceAdmission :=
    unary_cont_closed SUnary KUnary admissionRoute
  have supportUnary : UnaryHistory sourceSupport :=
    unary_cont_closed admissionUnary HUnary supportRoute
  have sourceSupportWitness :
      (fun row : BHist => hsame row sourceSupport ∧ UnaryHistory row) sourceSupport := by
    exact ⟨hsame_refl sourceSupport, supportUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceSupport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨ hsame row E ∨
              hsame row sourceAdmission ∨ hsame row sourceSupport)
          (fun row : BHist =>
            hsame row sourceSupport ∧ PkgSig bundle P pkg ∧
              PkgSig bundle sourceSupport pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceSupport sourceSupportWitness
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
      exact ⟨source.left, carrierPkg, supportPkg⟩
  }
  exact ⟨cert, admissionUnary, supportUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
