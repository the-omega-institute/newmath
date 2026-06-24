import BEDC.Derived.IntervalNewtonUp

namespace BEDC.Derived.IntervalNewtonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntervalNewtonKrawczykScope [AskSetup] [PackageSetup]
    {B F D N K V R H C P L narrowed radiusRead remainderRead consumerRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont N K narrowed ->
        Cont D R radiusRead ->
          Cont radiusRead V remainderRead ->
            Cont K V consumerRead ->
              Cont consumerRead R realRead ->
                PkgSig bundle realRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row B ∨ hsame row D ∨ hsame row N ∨ hsame row K ∨
                          hsame row V ∨ hsame row R ∨ hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont N K narrowed ∧ Cont D R radiusRead ∧
                          Cont radiusRead V remainderRead ∧ Cont K V consumerRead ∧
                            Cont consumerRead R realRead ∧ PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory narrowed ∧ UnaryHistory radiusRead ∧
                      UnaryHistory remainderRead ∧ UnaryHistory consumerRead ∧
                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier narrowedRoute radiusRoute remainderRoute consumerRoute realRoute realPkg
  obtain ⟨_unaryB, _unaryF, unaryD, unaryN, unaryK, unaryV, unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _validatedLocal, _provenancePkg, _localPkg⟩ := carrier
  have narrowedUnary : UnaryHistory narrowed :=
    unary_cont_closed unaryN unaryK narrowedRoute
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryD unaryR radiusRoute
  have remainderUnary : UnaryHistory remainderRead :=
    unary_cont_closed radiusUnary unaryV remainderRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed unaryK unaryV consumerRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed consumerUnary unaryR realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row D ∨ hsame row N ∨ hsame row K ∨
              hsame row V ∨ hsame row R ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N K narrowed ∧ Cont D R radiusRead ∧
              Cont radiusRead V remainderRead ∧ Cont K V consumerRead ∧
                Cont consumerRead R realRead ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, narrowedRoute, radiusRoute, remainderRoute, consumerRoute,
          realRoute, realPkg⟩
  }
  exact
    ⟨cert, narrowedUnary, radiusUnary, remainderUnary, consumerUnary, realUnary⟩

end BEDC.Derived.IntervalNewtonUp
