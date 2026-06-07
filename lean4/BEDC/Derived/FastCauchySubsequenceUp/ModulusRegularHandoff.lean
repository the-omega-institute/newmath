import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceModulusRegularHandoff [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W sealRead ->
                Cont sealRead N namedRead ->
                  PkgSig bundle namedRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row F ∨
                            hsame row R ∨ hsame row W ∨ hsame row E ∨
                              hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S M modulusRead ∧
                            Cont modulusRead Q selectorRead ∧
                              Cont selectorRead F fastRead ∧
                                Cont fastRead R regularRead ∧
                                  Cont regularRead W sealRead ∧
                                    Cont sealRead N namedRead ∧
                                      PkgSig bundle namedRead pkg)
                        hsame ∧ UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                      UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                        UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modulusRoute selectorRoute fastRoute regularRoute sealRoute nameRoute
    namedPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, unaryE, _unaryH, _unaryC,
    _unaryP, unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryS unaryM modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary unaryW sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
              hsame row W ∨ hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M modulusRead ∧ Cont modulusRead Q selectorRead ∧
              Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                Cont regularRead W sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, selectorRoute, fastRoute, regularRoute, sealRoute,
          nameRoute, namedPkg⟩
  }
  exact
    ⟨cert, modulusUnary, selectorUnary, fastUnary, regularUnary, sealUnary, namedUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
