import BEDC.Derived.RegularCauchyWindowFusionUp.TailWindowCoverage

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionDownstreamPackage [AskSetup] [PackageSetup]
    {R W S D E H _C P N seedWindow regularDyadic realSeal supportRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory W →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory E →
              UnaryHistory H →
                UnaryHistory N →
                  Cont R W seedWindow →
                    Cont S D regularDyadic →
                      Cont seedWindow regularDyadic realSeal →
                        Cont realSeal H supportRead →
                          Cont supportRead N downstreamRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle downstreamRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row downstreamRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row R ∨ hsame row W ∨ hsame row S ∨
                                        hsame row D ∨ hsame row E ∨ hsame row H ∨
                                          hsame row N ∨ hsame row seedWindow ∨
                                            hsame row regularDyadic ∨ hsame row realSeal ∨
                                              hsame row supportRead ∨
                                                hsame row downstreamRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont R W seedWindow ∧
                                        Cont S D regularDyadic ∧
                                          Cont seedWindow regularDyadic realSeal ∧
                                            Cont realSeal H supportRead ∧
                                              Cont supportRead N downstreamRead ∧
                                                PkgSig bundle downstreamRead pkg)
                                    hsame ∧
                                  UnaryHistory seedWindow ∧ UnaryHistory regularDyadic ∧
                                    UnaryHistory realSeal ∧ UnaryHistory supportRead ∧
                                      UnaryHistory downstreamRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rUnary wUnary sUnary dUnary _eUnary hUnary nUnary seedRoute regularRoute realRoute
    supportRoute downstreamRoute _packageRead downstreamPkg
  have seedUnary : UnaryHistory seedWindow :=
    unary_cont_closed rUnary wUnary seedRoute
  have regularUnary : UnaryHistory regularDyadic :=
    unary_cont_closed sUnary dUnary regularRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed seedUnary regularUnary realRoute
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed realUnary hUnary supportRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed supportUnary nUnary downstreamRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row N ∨ hsame row seedWindow ∨
                hsame row regularDyadic ∨ hsame row realSeal ∨ hsame row supportRead ∨
                  hsame row downstreamRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W seedWindow ∧ Cont S D regularDyadic ∧
              Cont seedWindow regularDyadic realSeal ∧ Cont realSeal H supportRead ∧
                Cont supportRead N downstreamRead ∧ PkgSig bundle downstreamRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro downstreamRead ⟨hsame_refl downstreamRead, downstreamUnary⟩
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
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, seedRoute, regularRoute, realRoute, supportRoute,
          downstreamRoute, downstreamPkg⟩
  }
  exact
    ⟨cert, seedUnary, regularUnary, realUnary, supportUnary, downstreamUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
