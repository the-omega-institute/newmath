import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_bind_route_classifier_stability [AskSetup] [PackageSetup]
    {A B C f g u H K L N bindRead resultRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationMonadCarrier A B C f g u H K L N ->
      Cont A f bindRead ->
        Cont bindRead C resultRead ->
          PkgSig bundle L pkg ->
            PkgSig bundle resultRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row resultRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont A f bindRead ∧ Cont bindRead C resultRead ∧
                      hsame row resultRead)
                  (fun row : BHist =>
                    PkgSig bundle L pkg ∧ PkgSig bundle resultRead pkg ∧
                      hsame row resultRead)
                  hsame ∧
                UnaryHistory bindRead ∧ UnaryHistory resultRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier bindRoute resultRoute ledgerPkg resultPkg
  obtain ⟨unaryA, unaryF, unaryG, _unaryU, routeB, routeC, _routeK, _routeL,
    _sameEndpoint⟩ := carrier
  have unaryB : UnaryHistory B :=
    unary_cont_closed unaryA unaryF routeB
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryB unaryG routeC
  have bindReadUnary : UnaryHistory bindRead :=
    unary_cont_closed unaryA unaryF bindRoute
  have resultReadUnary : UnaryHistory resultRead :=
    unary_cont_closed bindReadUnary unaryC resultRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row resultRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont A f bindRead ∧ Cont bindRead C resultRead ∧ hsame row resultRead)
          (fun row : BHist =>
            PkgSig bundle L pkg ∧ PkgSig bundle resultRead pkg ∧ hsame row resultRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro resultRead
        ⟨hsame_refl resultRead, resultReadUnary⟩
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
      exact ⟨bindRoute, resultRoute, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨ledgerPkg, resultPkg, source.left⟩
  }
  exact ⟨cert, bindReadUnary, resultReadUnary⟩

end BEDC.Derived.ContinuationMonadUp
