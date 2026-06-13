import BEDC.Derived.UpperRealUp.ObligationSurface

namespace BEDC.Derived.UpperRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpperRealCarrier_public_certificate [AskSetup] [PackageSetup]
    {U0 L W R E H C P N apartRead windowRead handoffRead sealRead transportRead
      replayRead namedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U0 ->
      UnaryHistory L ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont L U0 apartRead ->
                        Cont apartRead W windowRead ->
                          Cont windowRead R handoffRead ->
                            Cont handoffRead E sealRead ->
                              Cont sealRead H transportRead ->
                                Cont transportRead C replayRead ->
                                  Cont P N namedRead ->
                                    Cont replayRead namedRead publicRead ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle N pkg ->
                                          PkgSig bundle publicRead pkg ->
                                            SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row publicRead ∧
                                                    UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row U0 ∨ hsame row L ∨
                                                    hsame row W ∨ hsame row R ∨
                                                      hsame row E ∨ hsame row H ∨
                                                        hsame row C ∨ hsame row P ∨
                                                          hsame row N ∨
                                                            hsame row publicRead)
                                                (fun row : BHist =>
                                                  UnaryHistory row ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg ∧
                                                        PkgSig bundle publicRead pkg)
                                                hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro u0Unary lUnary wUnary rUnary eUnary hUnary cUnary pUnary nUnary apartRoute
    windowRoute handoffRoute sealRoute transportRoute replayRoute namedRoute
    publicRoute pkgP pkgN pkgPublic
  have apartUnary : UnaryHistory apartRead :=
    unary_cont_closed lUnary u0Unary apartRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed apartUnary wUnary windowRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed windowUnary rUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary eUnary sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary namedUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U0 ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
              PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pkgP, pkgN, pkgPublic⟩
  }
  exact ⟨cert, publicUnary⟩

theorem UpperRealCarrier_scoped_kernel_dependency_route [AskSetup] [PackageSetup]
    {U0 L W R E H C P N apartRead windowRead handoffRead sealRead transportRead
      replayRead namedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U0 ->
      UnaryHistory L ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont L U0 apartRead ->
                        Cont apartRead W windowRead ->
                          Cont windowRead R handoffRead ->
                            Cont handoffRead E sealRead ->
                              Cont sealRead H transportRead ->
                                Cont transportRead C replayRead ->
                                  Cont P N namedRead ->
                                    Cont replayRead namedRead publicRead ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle N pkg ->
                                          PkgSig bundle publicRead pkg ->
                                            UnaryHistory apartRead ∧
                                              UnaryHistory windowRead ∧
                                                UnaryHistory handoffRead ∧
                                                  UnaryHistory sealRead ∧
                                                    UnaryHistory transportRead ∧
                                                      UnaryHistory replayRead ∧
                                                        UnaryHistory namedRead ∧
                                                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro u0Unary lUnary wUnary rUnary eUnary hUnary cUnary pUnary nUnary apartRoute
    windowRoute handoffRoute sealRoute transportRoute replayRoute namedRoute
    publicRoute _pkgP _pkgN _pkgPublic
  have apartUnary : UnaryHistory apartRead :=
    unary_cont_closed lUnary u0Unary apartRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed apartUnary wUnary windowRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed windowUnary rUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary eUnary sealRoute
  have transportUnary : UnaryHistory transportRead :=
    unary_cont_closed sealUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary namedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed replayUnary namedUnary publicRoute
  exact
    ⟨apartUnary, windowUnary, handoffUnary, sealUnary, transportUnary, replayUnary,
      namedUnary, publicUnary⟩

theorem UpperRealCarrier_located_cut_bridge [AskSetup] [PackageSetup]
    {U0 L W R E H C P N apartRead windowRead handoffRead sealRead transportRead
      replayRead namedRead publicRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U0 ->
      UnaryHistory L ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont L U0 apartRead ->
                        Cont apartRead W windowRead ->
                          Cont windowRead R handoffRead ->
                            Cont handoffRead E sealRead ->
                              Cont sealRead H transportRead ->
                                Cont transportRead C replayRead ->
                                  Cont P N namedRead ->
                                    Cont replayRead namedRead publicRead ->
                                      Cont publicRead E locatedRead ->
                                        PkgSig bundle P pkg ->
                                          PkgSig bundle N pkg ->
                                            PkgSig bundle publicRead pkg ->
                                              UnaryHistory apartRead ∧
                                                UnaryHistory windowRead ∧
                                                  UnaryHistory handoffRead ∧
                                                    UnaryHistory sealRead ∧
                                                      UnaryHistory transportRead ∧
                                                        UnaryHistory replayRead ∧
                                                          UnaryHistory namedRead ∧
                                                            UnaryHistory publicRead ∧
                                                              UnaryHistory locatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro u0Unary lUnary wUnary rUnary eUnary hUnary cUnary pUnary nUnary apartRoute
    windowRoute handoffRoute sealRoute transportRoute replayRoute namedRoute publicRoute
    locatedRoute pkgP pkgN pkgPublic
  have route :=
    UpperRealCarrier_scoped_kernel_dependency_route (U0 := U0) (L := L) (W := W)
      (R := R) (E := E) (H := H) (C := C) (P := P) (N := N)
      (apartRead := apartRead) (windowRead := windowRead) (handoffRead := handoffRead)
      (sealRead := sealRead) (transportRead := transportRead) (replayRead := replayRead)
      (namedRead := namedRead) (publicRead := publicRead) (bundle := bundle) (pkg := pkg)
      u0Unary lUnary wUnary rUnary eUnary hUnary cUnary pUnary nUnary apartRoute windowRoute
      handoffRoute sealRoute transportRoute replayRoute namedRoute publicRoute pkgP pkgN
      pkgPublic
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed route.right.right.right.right.right.right.right eUnary locatedRoute
  exact
    ⟨route.left, route.right.left, route.right.right.left, route.right.right.right.left,
      route.right.right.right.right.left, route.right.right.right.right.right.left,
      route.right.right.right.right.right.right.left,
      route.right.right.right.right.right.right.right, locatedUnary⟩

theorem UpperRealCarrier_completeness_facing_consumer_route [AskSetup] [PackageSetup]
    {U0 L W R E H C P N apartRead windowRead handoffRead sealRead transportRead
      replayRead namedRead publicRead locatedRead completeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U0 ->
      UnaryHistory L ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont L U0 apartRead ->
                        Cont apartRead W windowRead ->
                          Cont windowRead R handoffRead ->
                            Cont handoffRead E sealRead ->
                              Cont sealRead H transportRead ->
                                Cont transportRead C replayRead ->
                                  Cont P N namedRead ->
                                    Cont replayRead namedRead publicRead ->
                                      Cont publicRead E locatedRead ->
                                        Cont locatedRead C completeRead ->
                                          PkgSig bundle P pkg ->
                                            PkgSig bundle N pkg ->
                                              PkgSig bundle publicRead pkg ->
                                                UnaryHistory apartRead ∧
                                                  UnaryHistory windowRead ∧
                                                    UnaryHistory handoffRead ∧
                                                      UnaryHistory sealRead ∧
                                                        UnaryHistory transportRead ∧
                                                          UnaryHistory replayRead ∧
                                                            UnaryHistory namedRead ∧
                                                              UnaryHistory publicRead ∧
                                                                UnaryHistory locatedRead ∧
                                                                  UnaryHistory completeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro u0Unary lUnary wUnary rUnary eUnary hUnary cUnary pUnary nUnary apartRoute
    windowRoute handoffRoute sealRoute transportRoute replayRoute namedRoute publicRoute
    locatedRoute completeRoute pkgP pkgN pkgPublic
  have route :=
    UpperRealCarrier_located_cut_bridge (U0 := U0) (L := L) (W := W)
      (R := R) (E := E) (H := H) (C := C) (P := P) (N := N)
      (apartRead := apartRead) (windowRead := windowRead) (handoffRead := handoffRead)
      (sealRead := sealRead) (transportRead := transportRead) (replayRead := replayRead)
      (namedRead := namedRead) (publicRead := publicRead) (locatedRead := locatedRead)
      (bundle := bundle) (pkg := pkg) u0Unary lUnary wUnary rUnary eUnary hUnary cUnary
      pUnary nUnary apartRoute windowRoute handoffRoute sealRoute transportRoute replayRoute
      namedRoute publicRoute locatedRoute pkgP pkgN pkgPublic
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed route.right.right.right.right.right.right.right.right cUnary completeRoute
  exact
    ⟨route.left, route.right.left, route.right.right.left, route.right.right.right.left,
      route.right.right.right.right.left, route.right.right.right.right.right.left,
      route.right.right.right.right.right.right.left,
      route.right.right.right.right.right.right.right.left,
      route.right.right.right.right.right.right.right.right, completeUnary⟩

end BEDC.Derived.UpperRealUp
