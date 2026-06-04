import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceSelectorRegularityPullback [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead pullbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont M Q modulusRead -> Cont modulusRead F selectorRead ->
        Cont selectorRead R fastRead -> Cont fastRead W regularRead ->
          Cont regularRead H pullbackRead -> PkgSig bundle pullbackRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row pullbackRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨ hsame row W ∨
                  hsame row H ∨ hsame row P ∨ hsame row N ∨ hsame row pullbackRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M Q modulusRead ∧
                  Cont modulusRead F selectorRead ∧ Cont selectorRead R fastRead ∧
                    Cont fastRead W regularRead ∧ Cont regularRead H pullbackRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle pullbackRead pkg)
              hsame ∧ UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory pullbackRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier modulusRoute selectorRoute fastRoute regularRoute pullbackRoute pullbackPkg
  obtain ⟨_unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, _unaryE, unaryH, _unaryC,
    unaryP, _unaryN, provenancePkg, _localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryQ modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary unaryF selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryR fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryW regularRoute
  have pullbackUnary : UnaryHistory pullbackRead :=
    unary_cont_closed regularUnary unaryH pullbackRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row pullbackRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨ hsame row W ∨
            hsame row H ∨ hsame row P ∨ hsame row N ∨ hsame row pullbackRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M Q modulusRead ∧ Cont modulusRead F selectorRead ∧
            Cont selectorRead R fastRead ∧ Cont fastRead W regularRead ∧
              Cont regularRead H pullbackRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle pullbackRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro pullbackRead ⟨hsame_refl pullbackRead, pullbackUnary⟩
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
        ⟨source.right, modulusRoute, selectorRoute, fastRoute, regularRoute,
          pullbackRoute, provenancePkg, pullbackPkg⟩
  }
  exact
    ⟨cert, modulusUnary, selectorUnary, fastUnary, regularUnary, pullbackUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
