import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformCompletionCommonWindowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCompletionCommonWindowCarrier [AskSetup] [PackageSetup]
    (U E S R D L F H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory U ∧ UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory R ∧
    UnaryHistory D ∧ UnaryHistory L ∧ UnaryHistory F ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont U E S ∧
        Cont S R D ∧ Cont D L F ∧ Cont H C P ∧ PkgSig bundle P pkg ∧
          PkgSig bundle N pkg

theorem UniformCompletionCommonWindowNameCertObligations [AskSetup] [PackageSetup]
    {U E S R D L F H C P N readbackRead budgetRead sealRead routeRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionCommonWindowCarrier U E S R D L F H C P N bundle pkg ->
      Cont S R readbackRead ->
        Cont readbackRead D budgetRead ->
          Cont budgetRead L sealRead ->
            Cont sealRead F routeRead ->
              Cont routeRead N namedRead ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row E ∨ hsame row S ∨ hsame row R ∨
                          hsame row D ∨ hsame row L ∨ hsame row F ∨ hsame row H ∨
                            hsame row C ∨ hsame row P ∨ hsame row N ∨
                              hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont S R readbackRead ∧
                          Cont readbackRead D budgetRead ∧ Cont budgetRead L sealRead ∧
                            Cont sealRead F routeRead ∧ Cont routeRead N namedRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                      hsame ∧ UnaryHistory readbackRead ∧ UnaryHistory budgetRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory routeRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier readbackRoute budgetRoute sealRoute routeRoute namedRoute namedPkg
  obtain ⟨unaryU, unaryE, unaryS, unaryR, unaryD, unaryL, unaryF, _unaryH, _unaryC,
    _unaryP, unaryN, _sourceRoute, _budgetSourceRoute, _functorRoute, _replayRoute,
    provenancePkg, localNamePkg⟩ := carrier
  have _sourceRows :
      UnaryHistory U ∧ UnaryHistory E ∧ UnaryHistory S ∧ UnaryHistory R ∧
        UnaryHistory D ∧ UnaryHistory L ∧ UnaryHistory F ∧ UnaryHistory N :=
    ⟨unaryU, unaryE, unaryS, unaryR, unaryD, unaryL, unaryF, unaryN⟩
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed unaryS unaryR readbackRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed readbackUnary unaryD budgetRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetUnary unaryL sealRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed sealUnary unaryF routeRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed routeUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row E ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row L ∨ hsame row F ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R readbackRead ∧
              Cont readbackRead D budgetRead ∧ Cont budgetRead L sealRead ∧
                Cont sealRead F routeRead ∧ Cont routeRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, readbackRoute, budgetRoute, sealRoute, routeRoute, namedRoute,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, readbackUnary, budgetUnary, sealUnary, routeUnary, namedUnary⟩

end BEDC.Derived.UniformCompletionCommonWindowUp
