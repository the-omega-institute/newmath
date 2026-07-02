import BEDC.Derived.FiniteWindowRealSeparationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowRealSeparationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteWindowRealSeparation_namecert_surface [AskSetup] [PackageSetup]
    {x : FiniteWindowRealSeparationUp}
    {W D S R H C P N route endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteWindowRealSeparationToEventFlow x =
        finiteWindowRealSeparationToEventFlow
          (FiniteWindowRealSeparationUp.mk W D S R H C P N) ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory S ->
            UnaryHistory R ->
              UnaryHistory N ->
                Cont W D S ->
                  Cont S R route ->
                    Cont route N endpoint ->
                      PkgSig bundle endpoint pkg ->
                        SemanticNameCert
                          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row endpoint ∧ Cont W D S ∧ Cont S R route ∧
                              Cont route N endpoint)
                          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _flowEq _unaryW _unaryD unaryS unaryR unaryN windowRoute separationRoute endpointRoute
    endpointPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed unaryS unaryR separationRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary unaryN endpointRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      exact ⟨source.left, windowRoute, separationRoute, endpointRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }

theorem FiniteWindowRealSeparation_window_refusal [AskSetup] [PackageSetup]
    {W D S R H C P N toleranceRead readbackRead separationRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
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
                        PkgSig bundle P pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                hsame row separationRead /\ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row W \/ hsame row D \/ hsame row S \/
                                  hsame row R \/ hsame row H \/ hsame row C \/
                                    hsame row P \/ hsame row N \/
                                      hsame row toleranceRead \/ hsame row readbackRead \/
                                        hsame row separationRead \/ hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row /\ Cont W D toleranceRead /\
                                  Cont toleranceRead S readbackRead /\
                                    Cont readbackRead R separationRead /\
                                      Cont separationRead N namedRead /\
                                        PkgSig bundle P pkg)
                              hsame /\
                            UnaryHistory toleranceRead /\ UnaryHistory readbackRead /\
                              UnaryHistory separationRead /\ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD unaryS unaryR _unaryP unaryN toleranceRoute readbackRoute
    separationRoute namedRoute pkgP
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
          (fun row : BHist => hsame row separationRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row W \/ hsame row D \/ hsame row S \/ hsame row R \/ hsame row H \/
              hsame row C \/ hsame row P \/ hsame row N \/ hsame row toleranceRead \/
                hsame row readbackRead \/ hsame row separationRead \/ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row /\ Cont W D toleranceRead /\
              Cont toleranceRead S readbackRead /\ Cont readbackRead R separationRead /\
                Cont separationRead N namedRead /\ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separationRead ⟨hsame_refl separationRead, separationUnary⟩
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
                          (Or.inr (Or.inl source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceRoute, readbackRoute, separationRoute, namedRoute, pkgP⟩
  }
  exact ⟨cert, toleranceUnary, readbackUnary, separationUnary, namedUnary⟩

theorem FiniteWindowRealSeparation_obligation_closure_route [AskSetup] [PackageSetup]
    {W D S R H C P N toleranceRead readbackRead separationRead namedRead
      closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
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
                        Cont namedRead P closureRead ->
                          PkgSig bundle P pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row W ∨ hsame row D ∨ hsame row S ∨
                                    hsame row R ∨ hsame row H ∨ hsame row C ∨
                                      hsame row P ∨ hsame row N ∨
                                        hsame row toleranceRead ∨ hsame row readbackRead ∨
                                          hsame row separationRead ∨ hsame row namedRead ∨
                                            hsame row closureRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont W D toleranceRead ∧
                                    Cont toleranceRead S readbackRead ∧
                                      Cont readbackRead R separationRead ∧
                                        Cont separationRead N namedRead ∧
                                          Cont namedRead P closureRead ∧
                                            PkgSig bundle P pkg)
                                hsame ∧ UnaryHistory closureRead := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD unaryS unaryR unaryP unaryN toleranceRoute readbackRoute
    separationRoute namedRoute closureRoute pkgP
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row toleranceRead ∨
                hsame row readbackRead ∨ hsame row separationRead ∨ hsame row namedRead ∨
                  hsame row closureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead ∧ Cont readbackRead R separationRead ∧
                Cont separationRead N namedRead ∧ Cont namedRead P closureRead ∧
                  PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro closureRead ⟨hsame_refl closureRead, closureUnary⟩
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
        cases sameRows
        exact source
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
      exact
        ⟨source.right, toleranceRoute, readbackRoute, separationRoute, namedRoute,
          closureRoute, pkgP⟩
  }
  exact ⟨cert, closureUnary⟩

theorem FiniteWindowRealSeparation_shared_window_obligation [AskSetup] [PackageSetup]
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
                          PkgSig bundle P pkg ->
                            x = FiniteWindowRealSeparationUp.mk W D S R H C P N ∧
                              UnaryHistory namedRead ∧
                                SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row separationRead ∧ UnaryHistory row)
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
                                            PkgSig bundle P pkg)
                                  hsame := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory ChapterTasteGate
  intro flowEq unaryW unaryD unaryS unaryR unaryP unaryN toleranceRoute readbackRoute
    separationRoute namedRoute pkgP
  have flowInjective :
      ∀ x y : FiniteWindowRealSeparationUp,
        finiteWindowRealSeparationToEventFlow x =
          finiteWindowRealSeparationToEventFlow y → x = y :=
    FiniteWindowRealSeparationTasteGate_single_carrier_alignment.right.right.left
  have carrierEq : x = FiniteWindowRealSeparationUp.mk W D S R H C P N :=
    flowInjective x (FiniteWindowRealSeparationUp.mk W D S R H C P N) flowEq
  have windowRefusal :=
    FiniteWindowRealSeparation_window_refusal
      (W := W) (D := D) (S := S) (R := R) (H := H) (C := C) (P := P) (N := N)
      (toleranceRead := toleranceRead) (readbackRead := readbackRead)
      (separationRead := separationRead) (namedRead := namedRead)
      (bundle := bundle) (pkg := pkg)
      unaryW unaryD unaryS unaryR unaryP unaryN toleranceRoute readbackRoute
      separationRoute namedRoute pkgP
  exact ⟨carrierEq, windowRefusal.right.right.right.right, windowRefusal.left⟩

theorem FiniteWindowRealSeparation_window_budget_determinacy [AskSetup] [PackageSetup]
    {W D S R R' H C P N C' P' N' toleranceRead readbackRead separationRead
      separationRead' namedRead namedRead' budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W -> UnaryHistory D -> UnaryHistory S -> UnaryHistory R ->
      UnaryHistory R' -> UnaryHistory H -> UnaryHistory N ->
        Cont W D toleranceRead -> Cont toleranceRead S readbackRead ->
          Cont readbackRead R separationRead -> Cont readbackRead R' separationRead' ->
            Cont separationRead N namedRead -> Cont separationRead' N namedRead' ->
              Cont namedRead H budgetRead -> PkgSig bundle budgetRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
                        hsame row separationRead ∨ hsame row separationRead' ∨
                          hsame row budgetRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W D toleranceRead ∧
                        Cont toleranceRead S readbackRead ∧ Cont namedRead H budgetRead ∧
                          PkgSig bundle budgetRead pkg)
                    hsame ∧ UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD unaryS unaryR unaryR' unaryH unaryN toleranceRoute readbackRoute
    separationRoute separationRoute' namedRoute _namedRoute' budgetRoute budgetSig
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryS readbackRoute
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed readbackUnary unaryR separationRoute
  have _separationUnary' : UnaryHistory separationRead' :=
    unary_cont_closed readbackUnary unaryR' separationRoute'
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed separationUnary unaryN namedRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed namedUnary unaryH budgetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row H ∨
              hsame row separationRead ∨ hsame row separationRead' ∨ hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead ∧ Cont namedRead H budgetRead ∧
                PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceRoute, readbackRoute, budgetRoute, budgetSig⟩
  }
  exact ⟨cert, budgetUnary⟩

theorem FiniteWindowRealSeparation_shared_budget_normalization [AskSetup] [PackageSetup]
    {W D S R R' H C P N C' P' N' toleranceRead readbackRead separationRead namedRead
      normalizedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W -> UnaryHistory D -> UnaryHistory S -> UnaryHistory R ->
      UnaryHistory H -> UnaryHistory P -> UnaryHistory N ->
        Cont W D toleranceRead -> Cont toleranceRead S readbackRead ->
          Cont readbackRead R separationRead -> Cont separationRead N namedRead ->
            Cont namedRead P normalizedRead -> PkgSig bundle normalizedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row normalizedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                      hsame row H ∨ hsame row namedRead ∨ hsame row normalizedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W D toleranceRead ∧
                      Cont toleranceRead S readbackRead ∧ Cont readbackRead R separationRead ∧
                        Cont separationRead N namedRead ∧ Cont namedRead P normalizedRead ∧
                          PkgSig bundle normalizedRead pkg)
                  hsame ∧ UnaryHistory normalizedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD unaryS unaryR _unaryH unaryP unaryN toleranceRoute readbackRoute
    separationRoute namedRoute normalizedRoute normalizedSig
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryS readbackRoute
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed readbackUnary unaryR separationRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed separationUnary unaryN namedRoute
  have normalizedUnary : UnaryHistory normalizedRead :=
    unary_cont_closed namedUnary unaryP normalizedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalizedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
              hsame row namedRead ∨ hsame row normalizedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead ∧ Cont readbackRead R separationRead ∧
                Cont separationRead N namedRead ∧ Cont namedRead P normalizedRead ∧
                  PkgSig bundle normalizedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro normalizedRead ⟨hsame_refl normalizedRead, normalizedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceRoute, readbackRoute, separationRoute, namedRoute,
        normalizedRoute, normalizedSig⟩
  }
  exact ⟨cert, normalizedUnary⟩

theorem FiniteWindowRealSeparation_obligation_surface
    {W D S R H C P N wd ds sr hc cp : BHist} :
    UnaryHistory W →
      UnaryHistory D →
        UnaryHistory S →
          UnaryHistory R →
            UnaryHistory H →
              UnaryHistory C →
                UnaryHistory P →
                  UnaryHistory N →
                    Cont W D wd →
                      Cont wd S ds →
                        Cont ds R sr →
                          Cont H C hc →
                            Cont hc P cp →
                              UnaryHistory sr ∧ Cont W D wd ∧ Cont wd S ds ∧
                                Cont ds R sr ∧ Cont H C hc ∧ Cont hc P cp ∧
                                  UnaryHistory N := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryW unaryD unaryS unaryR _unaryH _unaryC _unaryP unaryN wdRoute dsRoute
    srRoute hcRoute cpRoute
  have wdUnary : UnaryHistory wd :=
    unary_cont_closed unaryW unaryD wdRoute
  have dsUnary : UnaryHistory ds :=
    unary_cont_closed wdUnary unaryS dsRoute
  have srUnary : UnaryHistory sr :=
    unary_cont_closed dsUnary unaryR srRoute
  exact ⟨srUnary, wdRoute, dsRoute, srRoute, hcRoute, cpRoute, unaryN⟩

theorem FiniteWindowRealSeparation_common_window_exactness [AskSetup] [PackageSetup]
    {x y : FiniteWindowRealSeparationUp}
    {W D S R R' H H' C P N C' P' N' toleranceRead readbackRead separationRead
      separationRead' namedRead namedRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    finiteWindowRealSeparationToEventFlow x =
        finiteWindowRealSeparationToEventFlow
          (FiniteWindowRealSeparationUp.mk W D S R H C P N) ->
      finiteWindowRealSeparationToEventFlow y =
          finiteWindowRealSeparationToEventFlow
            (FiniteWindowRealSeparationUp.mk W D S R' H' C' P' N') ->
        UnaryHistory W -> UnaryHistory D -> UnaryHistory S -> UnaryHistory R ->
          UnaryHistory R' -> UnaryHistory N -> Cont W D toleranceRead ->
            Cont toleranceRead S readbackRead ->
              Cont readbackRead R separationRead ->
                Cont readbackRead R' separationRead' ->
                  Cont separationRead N namedRead ->
                    Cont separationRead' N namedRead' ->
                      PkgSig bundle namedRead pkg ->
                        x = FiniteWindowRealSeparationUp.mk W D S R H C P N ∧
                          y = FiniteWindowRealSeparationUp.mk W D S R' H' C' P' N' ∧
                            UnaryHistory separationRead ∧
                              UnaryHistory separationRead' ∧
                                SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row readbackRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row W ∨ hsame row D ∨ hsame row S ∨
                                      hsame row readbackRead ∨
                                        hsame row separationRead ∨
                                          hsame row separationRead')
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont W D toleranceRead ∧
                                      Cont toleranceRead S readbackRead)
                                  hsame := by
  -- BEDC touchpoint anchor: FiniteWindowRealSeparationUp BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro flowX flowY unaryW unaryD unaryS unaryR unaryR' _unaryN toleranceRoute
    readbackRoute separationRoute separationRoute' _namedRoute _namedRoute' _pkgNamed
  have roundTrip :
      ∀ z : FiniteWindowRealSeparationUp,
        finiteWindowRealSeparationFromEventFlow
          (finiteWindowRealSeparationToEventFlow z) = some z :=
    FiniteWindowRealSeparationTasteGate_single_carrier_alignment.right.left
  have xExact : x = FiniteWindowRealSeparationUp.mk W D S R H C P N :=
    Option.some.inj
      (Eq.trans (roundTrip x).symm
        (Eq.trans (congrArg finiteWindowRealSeparationFromEventFlow flowX)
          (roundTrip (FiniteWindowRealSeparationUp.mk W D S R H C P N))))
  have yExact : y = FiniteWindowRealSeparationUp.mk W D S R' H' C' P' N' :=
    Option.some.inj
      (Eq.trans (roundTrip y).symm
        (Eq.trans (congrArg finiteWindowRealSeparationFromEventFlow flowY)
          (roundTrip (FiniteWindowRealSeparationUp.mk W D S R' H' C' P' N'))))
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryS readbackRoute
  have separationUnary : UnaryHistory separationRead :=
    unary_cont_closed readbackUnary unaryR separationRoute
  have separationUnary' : UnaryHistory separationRead' :=
    unary_cont_closed readbackUnary unaryR' separationRoute'
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row D ∨ hsame row S ∨ hsame row readbackRead ∨
              hsame row separationRead ∨ hsame row separationRead')
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D toleranceRead ∧
              Cont toleranceRead S readbackRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro readbackRead ⟨hsame_refl readbackRead, readbackUnary⟩
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
      right; right; right; left
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceRoute, readbackRoute⟩
  }
  exact ⟨xExact, yExact, separationUnary, separationUnary', cert⟩

end BEDC.Derived.FiniteWindowRealSeparationUp
