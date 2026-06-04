import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricPrefixCauchyThreadCompleteness [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead radiusRead ultrametricRead completeRead
      threadRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont S B prefixRead →
        Cont ultrametricRead R completeRead →
          Cont completeRead C threadRead →
            PkgSig bundle threadRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row threadRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨
                      hsame row R ∨ hsame row C ∨ hsame row prefixRead ∨
                        hsame row radiusRead ∨ hsame row ultrametricRead ∨
                          hsame row completeRead ∨ hsame row threadRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S B prefixRead ∧
                      Cont radiusRead D ultrametricRead ∧
                        Cont ultrametricRead R completeRead ∧
                          Cont completeRead C threadRead ∧
                            PkgSig bundle threadRead pkg)
                  hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory radiusRead ∧
                UnaryHistory ultrametricRead ∧ UnaryHistory completeRead ∧
                  UnaryHistory threadRead := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier prefixRoute completeRoute threadRoute threadPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, _unaryU, _unaryH, unaryC,
    _unaryP, _unaryN, carrierRadiusRoute, ultrametricRoute, _provenancePkg,
      _localNamePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryS unaryB prefixRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB carrierRadiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed ultrametricUnary unaryR completeRoute
  have threadUnary : UnaryHistory threadRead :=
    unary_cont_closed completeUnary unaryC threadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row threadRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row B ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row C ∨ hsame row prefixRead ∨ hsame row radiusRead ∨
                hsame row ultrametricRead ∨ hsame row completeRead ∨ hsame row threadRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S B prefixRead ∧ Cont radiusRead D ultrametricRead ∧
              Cont ultrametricRead R completeRead ∧ Cont completeRead C threadRead ∧
                PkgSig bundle threadRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro threadRead ⟨hsame_refl threadRead, threadUnary⟩
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
        ⟨source.right, prefixRoute, ultrametricRoute, completeRoute, threadRoute,
          threadPkg⟩
  }
  exact
    ⟨cert, prefixUnary, radiusUnary, ultrametricUnary, completeUnary, threadUnary⟩

end BEDC.Derived.BaireMetricUp
