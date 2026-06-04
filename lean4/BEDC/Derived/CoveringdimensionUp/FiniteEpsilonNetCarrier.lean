import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem covering_dimension_finite_epsilon_net_carrier_semantic_namecert_boundary
    [AskSetup] [PackageSetup]
    {K E C R O L H T P N coverRead refineRead orderRead ledgerRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K ->
      UnaryHistory E ->
        UnaryHistory C ->
          UnaryHistory R ->
            UnaryHistory O ->
              UnaryHistory L ->
                UnaryHistory N ->
                  Cont K E coverRead ->
                    Cont coverRead C refineRead ->
                      Cont refineRead R orderRead ->
                        Cont orderRead O ledgerRead ->
                          Cont ledgerRead N namedRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row K ∨ hsame row E ∨ hsame row C ∨
                                        hsame row R ∨ hsame row O ∨ hsame row L ∨
                                          hsame row P ∨ hsame row N ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont K E coverRead ∧
                                        Cont coverRead C refineRead ∧
                                          Cont refineRead R orderRead ∧
                                            Cont orderRead O ledgerRead ∧
                                              Cont ledgerRead N namedRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle N pkg)
                                    hsame ∧
                                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro unaryK unaryE unaryC unaryR unaryO _unaryL unaryN coverRoute refineRoute orderRoute
    ledgerRoute namedRoute provenancePkg namedPkg
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed unaryK unaryE coverRoute
  have refineUnary : UnaryHistory refineRead :=
    unary_cont_closed coverUnary unaryC refineRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed refineUnary unaryR orderRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed orderUnary unaryO ledgerRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed ledgerUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨ hsame row O ∨
              hsame row L ∨ hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K E coverRead ∧ Cont coverRead C refineRead ∧
              Cont refineRead R orderRead ∧ Cont orderRead O ledgerRead ∧
                Cont ledgerRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
        ⟨source.right, coverRoute, refineRoute, orderRoute, ledgerRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
