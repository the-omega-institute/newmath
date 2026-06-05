import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalCompactMetricUniformBarScope [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N compactRead uniformRead barRead modulusRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg →
      Cont C B compactRead →
        Cont compactRead eps uniformRead →
          Cont F D barRead →
            Cont W M modulusRead →
              Cont modulusRead N namedRead →
                PkgSig bundle P pkg →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row C ∨ hsame row B ∨ hsame row eps ∨ hsame row F ∨
                            hsame row D ∨ hsame row W ∨ hsame row M ∨ hsame row N ∨
                              hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont C B compactRead ∧
                            Cont compactRead eps uniformRead ∧ Cont F D barRead ∧
                              Cont W M modulusRead ∧ Cont modulusRead N namedRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                        hsame ∧
                      UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
                        UnaryHistory barRead ∧ UnaryHistory modulusRead ∧
                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute uniformRoute barRoute modulusRoute namedRoute
    provenancePkg namedPkg
  obtain ⟨cUnary, fUnary, epsUnary, bUnary, dUnary, wUnary, mUnary, _hUnary, _kUnary,
    _pUnary, nUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _carrierProvenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed cUnary bUnary compactRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary epsUnary uniformRoute
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed fUnary dUnary barRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed wUnary mUnary modulusRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed modulusUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row B ∨ hsame row eps ∨ hsame row F ∨ hsame row D ∨
              hsame row W ∨ hsame row M ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C B compactRead ∧
              Cont compactRead eps uniformRead ∧ Cont F D barRead ∧
                Cont W M modulusRead ∧ Cont modulusRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactRoute, uniformRoute, barRoute, modulusRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, compactUnary, uniformUnary, barUnary, modulusUnary, namedUnary⟩

end BEDC.Derived.FanfunctionalUp
