import BEDC.Derived.ParsevalUp.NameCertObligations

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalRootRealSealNonescape [AskSetup] [PackageSetup]
    {F S I E R D L H C P N coefficientRead integralRead dyadicRead sealRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory S →
        UnaryHistory I →
          UnaryHistory E →
            UnaryHistory R →
              UnaryHistory D →
                UnaryHistory L →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory N →
                        Cont F S coefficientRead →
                          Cont I E integralRead →
                            Cont coefficientRead R dyadicRead →
                              Cont dyadicRead L sealRead →
                                Cont sealRead N namedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row F ∨ hsame row S ∨
                                              hsame row I ∨ hsame row E ∨
                                                hsame row R ∨ hsame row D ∨
                                                  hsame row L ∨ hsame row H ∨
                                                    hsame row C ∨ hsame row N ∨
                                                      hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont F S coefficientRead ∧
                                                Cont I E integralRead ∧
                                                  Cont coefficientRead R dyadicRead ∧
                                                    Cont dyadicRead L sealRead ∧
                                                      Cont sealRead N namedRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory coefficientRead ∧
                                          UnaryHistory integralRead ∧
                                            UnaryHistory dyadicRead ∧
                                              UnaryHistory sealRead ∧
                                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fUnary sUnary iUnary eUnary rUnary _dUnary lUnary _hUnary _cUnary nUnary
    coefficientRoute integralRoute dyadicRoute sealRoute namedRoute provenancePkg namePkg
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fUnary sUnary coefficientRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed iUnary eUnary integralRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed coefficientUnary rUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary lUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F S coefficientRead ∧ Cont I E integralRead ∧
              Cont coefficientRead R dyadicRead ∧ Cont dyadicRead L sealRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coefficientRoute, integralRoute, dyadicRoute, sealRoute,
          namedRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, coefficientUnary, integralUnary, dyadicUnary, sealUnary, namedUnary⟩

end BEDC.Derived.ParsevalUp
