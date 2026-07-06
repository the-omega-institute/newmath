import BEDC.Derived.LocatedIntervalBisectionUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocatedIntervalBisectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedIntervalBisectionNestedWindowRoute [AskSetup] [PackageSetup]
    {left right midpoint sign window nestedRead routeRead _provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory left ->
      UnaryHistory right ->
        UnaryHistory midpoint ->
          UnaryHistory sign ->
            UnaryHistory window ->
              Cont left right midpoint ->
                Cont midpoint sign nestedRead ->
                  Cont nestedRead window routeRead ->
                    PkgSig bundle routeRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row left ∨ hsame row right ∨ hsame row midpoint ∨
                              hsame row sign ∨ hsame row window ∨ hsame row nestedRead ∨
                                hsame row routeRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont left right midpoint ∧
                              Cont midpoint sign nestedRead ∧
                                Cont nestedRead window routeRead ∧
                                  PkgSig bundle routeRead pkg)
                          hsame ∧
                        UnaryHistory nestedRead ∧ UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro _leftUnary _rightUnary midpointUnary signUnary windowUnary
    leftRightMidpoint midpointSignNested nestedWindowRoute routePkg
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed midpointUnary signUnary midpointSignNested
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed nestedUnary windowUnary nestedWindowRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row left ∨ hsame row right ∨ hsame row midpoint ∨ hsame row sign ∨
              hsame row window ∨ hsame row nestedRead ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont left right midpoint ∧ Cont midpoint sign nestedRead ∧
              Cont nestedRead window routeRead ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
                  (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, leftRightMidpoint, midpointSignNested, nestedWindowRoute,
          routePkg⟩
  }
  exact ⟨cert, nestedUnary, routeUnary⟩

theorem LocatedIntervalBisectionNestedWindowRoute_carrier_readback [AskSetup] [PackageSetup]
    {left right midpoint sign window nestedRead routeRead _provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory left ->
      UnaryHistory right ->
        UnaryHistory midpoint ->
          UnaryHistory sign ->
            UnaryHistory window ->
              Cont left right midpoint ->
                Cont midpoint sign nestedRead ->
                  Cont nestedRead window routeRead ->
                    PkgSig bundle routeRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row left ∨ hsame row right ∨ hsame row midpoint ∨
                              hsame row sign ∨ hsame row window ∨ hsame row nestedRead ∨
                                hsame row routeRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont left right midpoint ∧
                              Cont midpoint sign nestedRead ∧
                                Cont nestedRead window routeRead ∧
                                  PkgSig bundle routeRead pkg)
                          hsame ∧
                        locatedIntervalBisectionFromEventFlow
                            (locatedIntervalBisectionToEventFlow
                              (LocatedIntervalBisectionUp.mk left right midpoint sign window
                                nestedRead routeRead _provenance routeRead routeRead)) =
                          some
                            (LocatedIntervalBisectionUp.mk left right midpoint sign window
                              nestedRead routeRead _provenance routeRead routeRead) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont ChapterTasteGate SemanticNameCert
  intro leftUnary rightUnary midpointUnary signUnary windowUnary
    leftRightMidpoint midpointSignNested nestedWindowRoute routePkg
  have routeCert :=
    LocatedIntervalBisectionNestedWindowRoute
      (left := left) (right := right) (midpoint := midpoint) (sign := sign)
      (window := window) (nestedRead := nestedRead) (routeRead := routeRead)
      (_provenance := _provenance) (bundle := bundle) (pkg := pkg)
      leftUnary rightUnary midpointUnary signUnary windowUnary
      leftRightMidpoint midpointSignNested nestedWindowRoute routePkg
  have alignment := LocatedIntervalBisectionTasteGate_single_carrier_alignment
  exact ⟨routeCert.left, alignment.right.left _⟩

end BEDC.Derived.LocatedIntervalBisectionUp
