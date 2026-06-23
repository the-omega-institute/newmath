import BEDC.Derived.RegularCauchyWindowFusionUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionScopedKernelRoute [AskSetup] [PackageSetup]
    {R W S D E H C P N seedRead regularRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory S ->
          UnaryHistory D ->
            UnaryHistory E ->
              UnaryHistory H ->
                Cont R W seedRead ->
                  Cont seedRead S regularRead ->
                    Cont regularRead D sealRead ->
                      Cont sealRead E named ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                              (fun row : BHist => hsame row named ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row W ∨ hsame row S ∨
                                  hsame row D ∨ hsame row E ∨ hsame row H ∨
                                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                                      hsame row named)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont R W seedRead ∧
                                  Cont seedRead S regularRead ∧
                                    Cont regularRead D sealRead ∧
                                      Cont sealRead E named ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                              UnaryHistory seedRead ∧ UnaryHistory regularRead ∧
                                UnaryHistory sealRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro rUnary wUnary sUnary dUnary eUnary _hUnary seedRoute regularRoute sealRoute
    namedRoute pkgP pkgN
  have seedUnary : UnaryHistory seedRead :=
    unary_cont_closed rUnary wUnary seedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed seedUnary sUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary dUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sealUnary eUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W seedRead ∧ Cont seedRead S regularRead ∧
              Cont regularRead D sealRead ∧ Cont sealRead E named ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, seedRoute, regularRoute, sealRoute, namedRoute, pkgP,
          pkgN⟩
  }
  exact ⟨cert, seedUnary, regularUnary, sealUnary, namedUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
