import BEDC.Derived.FiniteWindowRealSeparationUp.NameCertSurface

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWindowRealSeparation_scoped_kernel_route [AskSetup] [PackageSetup]
    {x : FiniteWindowRealSeparationUp}
    {W D S R H C P N toleranceRead readbackRead separationRead namedRead closureRead
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteWindowRealSeparationToEventFlow x =
        finiteWindowRealSeparationToEventFlow
          (FiniteWindowRealSeparationUp.mk W D S R H C P N) ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory H ->
                UnaryHistory P ->
                  UnaryHistory N ->
                    Cont W D toleranceRead ->
                      Cont toleranceRead S readbackRead ->
                        Cont readbackRead R separationRead ->
                          Cont separationRead N namedRead ->
                            Cont namedRead P closureRead ->
                              Cont closureRead H scopedRead ->
                                PkgSig bundle scopedRead pkg ->
                                  x = FiniteWindowRealSeparationUp.mk W D S R H C P N ∧
                                    UnaryHistory scopedRead ∧
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row scopedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row W ∨ hsame row D ∨ hsame row S ∨
                                            hsame row R ∨ hsame row H ∨ hsame row P ∨
                                              hsame row N ∨ hsame row toleranceRead ∨
                                                hsame row readbackRead ∨
                                                  hsame row separationRead ∨
                                                    hsame row namedRead ∨
                                                      hsame row closureRead ∨
                                                        hsame row scopedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont W D toleranceRead ∧
                                            Cont toleranceRead S readbackRead ∧
                                              Cont readbackRead R separationRead ∧
                                                Cont separationRead N namedRead ∧
                                                  Cont namedRead P closureRead ∧
                                                    Cont closureRead H scopedRead ∧
                                                      PkgSig bundle scopedRead pkg)
                                        hsame := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory ChapterTasteGate
  intro flowEq unaryW unaryD unaryS unaryR unaryH unaryP unaryN toleranceRoute
    readbackRoute separationRoute namedRoute closureRoute scopedRoute scopedPkg
  have flowInjective :
      ∀ x y : FiniteWindowRealSeparationUp,
        finiteWindowRealSeparationToEventFlow x =
          finiteWindowRealSeparationToEventFlow y → x = y :=
    FiniteWindowRealSeparationTasteGate_single_carrier_alignment.right.right.left
  have carrierEq : x = FiniteWindowRealSeparationUp.mk W D S R H C P N :=
    flowInjective x (FiniteWindowRealSeparationUp.mk W D S R H C P N) flowEq
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryS readbackRoute
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed readbackUnary unaryR separationRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed separationUnary unaryN namedRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed namedUnary unaryP closureRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed closureUnary unaryH scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
              hsame row H ∨ hsame row P ∨ hsame row N ∨ hsame row toleranceRead ∨
                hsame row readbackRead ∨ hsame row separationRead ∨ hsame row namedRead ∨
                  hsame row closureRead ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead ∧ Cont readbackRead R separationRead ∧
                Cont separationRead N namedRead ∧ Cont namedRead P closureRead ∧
                  Cont closureRead H scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
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
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceRoute, readbackRoute, separationRoute, namedRoute,
        closureRoute, scopedRoute, scopedPkg⟩
  }
  exact ⟨carrierEq, scopedUnary, cert⟩

theorem FiniteWindowRealSeparation_witness_exhaustion [AskSetup] [PackageSetup]
    {x : FiniteWindowRealSeparationUp}
    {W D S R H C P N toleranceRead readbackRead separationRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteWindowRealSeparationToEventFlow x =
        finiteWindowRealSeparationToEventFlow
          (FiniteWindowRealSeparationUp.mk W D S R H C P N) ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory P ->
                UnaryHistory N ->
                  Cont W D toleranceRead ->
                    Cont toleranceRead S readbackRead ->
                      Cont readbackRead R separationRead ->
                        Cont separationRead N namedRead ->
                          PkgSig bundle namedRead pkg ->
                            x = FiniteWindowRealSeparationUp.mk W D S R H C P N ∧
                              UnaryHistory namedRead ∧
                                SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row W ∨ hsame row D ∨ hsame row S ∨
                                      hsame row R ∨ hsame row H ∨ hsame row C ∨
                                        hsame row P ∨ hsame row N ∨
                                          hsame row toleranceRead ∨
                                            hsame row readbackRead ∨
                                              hsame row separationRead ∨
                                                hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont W D toleranceRead ∧
                                      Cont toleranceRead S readbackRead ∧
                                        Cont readbackRead R separationRead ∧
                                          Cont separationRead N namedRead ∧
                                            PkgSig bundle namedRead pkg)
                                  hsame := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory ChapterTasteGate
  intro flowEq unaryW unaryD unaryS unaryR _unaryP unaryN toleranceRoute readbackRoute
    separationRoute namedRoute namedPkg
  have flowInjective :
      ∀ x y : FiniteWindowRealSeparationUp,
        finiteWindowRealSeparationToEventFlow x =
          finiteWindowRealSeparationToEventFlow y → x = y :=
    FiniteWindowRealSeparationTasteGate_single_carrier_alignment.right.right.left
  have carrierEq : x = FiniteWindowRealSeparationUp.mk W D S R H C P N :=
    flowInjective x (FiniteWindowRealSeparationUp.mk W D S R H C P N) flowEq
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryS readbackRoute
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed readbackUnary unaryR separationRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed separationUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row toleranceRead ∨ hsame row readbackRead ∨
                  hsame row separationRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead ∧ Cont readbackRead R separationRead ∧
                Cont separationRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
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
      exact ⟨source.right, toleranceRoute, readbackRoute, separationRoute, namedRoute,
        namedPkg⟩
  }
  exact ⟨carrierEq, namedUnary, cert⟩

end BEDC.Derived.FiniteWindowRealSeparationUp
