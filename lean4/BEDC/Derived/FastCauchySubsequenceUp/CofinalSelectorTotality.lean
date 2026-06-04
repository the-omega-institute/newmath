import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceCofinalSelectorTotality [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N precisionRead selectorRead fastRead regularRead readbackRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M precisionRead ->
        Cont precisionRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W readbackRead ->
                Cont readbackRead E realRead ->
                  PkgSig bundle realRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
                            hsame row W ∨ hsame row E ∨ hsame row selectorRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont precisionRead Q selectorRead ∧
                            Cont selectorRead F fastRead ∧
                              Cont fastRead R regularRead ∧
                                Cont regularRead W readbackRead ∧
                                  Cont readbackRead E realRead ∧
                                    PkgSig bundle realRead pkg)
                        hsame ∧
                      UnaryHistory precisionRead ∧ UnaryHistory selectorRead ∧
                        UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory readbackRead ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: FastCauchySubsequenceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier precisionRoute selectorRoute fastRoute regularRoute readbackRoute realRoute
    realPkg
  obtain ⟨unaryS, unaryM, unaryQ, unaryF, unaryR, unaryW, unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have precisionUnary : UnaryHistory precisionRead :=
    unary_cont_closed unaryS unaryM precisionRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed precisionUnary unaryQ selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary unaryF fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary unaryR regularRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed regularUnary unaryW readbackRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary unaryE realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row F ∨ hsame row R ∨
              hsame row W ∨ hsame row E ∨ hsame row selectorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont precisionRead Q selectorRead ∧
              Cont selectorRead F fastRead ∧ Cont fastRead R regularRead ∧
                Cont regularRead W readbackRead ∧ Cont readbackRead E realRead ∧
                  PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectorRead ⟨hsame_refl selectorRead, selectorUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectorRoute, fastRoute, regularRoute, readbackRoute, realRoute,
          realPkg⟩
  }
  exact
    ⟨cert, precisionUnary, selectorUnary, fastUnary, regularUnary, readbackUnary,
      realUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
