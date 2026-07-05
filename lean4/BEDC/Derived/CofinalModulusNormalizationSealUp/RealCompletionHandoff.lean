import BEDC.Derived.CofinalModulusNormalizationSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.CofinalModulusNormalizationSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CofinalModulusNormalizationSeal_real_completion_handoff
    {A B M W D R E H C P L N sharedRead dyadicRead regularRead sealRead terminalRead :
      BHist} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] →
      Cont A B M →
        Cont M W sharedRead →
          Cont sharedRead D dyadicRead →
            Cont dyadicRead R regularRead →
              Cont regularRead E sealRead →
                Cont sealRead L terminalRead →
                  hsame terminalRead
                    (append (append (append (append (append (append A B) W) D) R) E) L) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _fieldsExact routeAB routeShared routeDyadic routeRegular routeSeal routeTerminal
  cases routeAB
  cases routeShared
  cases routeDyadic
  cases routeRegular
  cases routeSeal
  cases routeTerminal
  rfl

theorem CofinalModulusNormalizationSeal_ledger_nonescape
    {A B M W D R E H C P L N sharedRead dyadicRead regularRead sealRead ledgerRead
      namedRead : BHist} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] →
      Cont A B M →
        Cont M W sharedRead →
          Cont sharedRead D dyadicRead →
            Cont dyadicRead R regularRead →
              Cont regularRead E sealRead →
                Cont sealRead L ledgerRead →
                  Cont ledgerRead N namedRead →
                    hsame namedRead
                      (append (append (append (append (append (append (append A B) W) D) R) E)
                        L) N) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _fieldsExact routeAB routeShared routeDyadic routeRegular routeSeal routeLedger routeName
  cases routeAB
  cases routeShared
  cases routeDyadic
  cases routeRegular
  cases routeSeal
  cases routeLedger
  cases routeName
  rfl

theorem CofinalModulusNormalizationSeal_obligation_row_exactness
    {A B M W D R E H C P L N sharedRead dyadicRead regularRead sealRead ledgerRead
      namedRead : BHist} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] →
      Cont A B M →
        Cont M W sharedRead →
          Cont sharedRead D dyadicRead →
            Cont dyadicRead R regularRead →
              Cont regularRead E sealRead →
                Cont sealRead L ledgerRead →
                  Cont ledgerRead N namedRead →
                    hsame namedRead
                        (append (append (append (append (append (append (append A B) W) D) R)
                          E) L) N) ∧
                      hsame ledgerRead
                        (append (append (append (append (append (append A B) W) D) R) E)
                          L) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _fieldsExact routeAB routeShared routeDyadic routeRegular routeSeal routeLedger routeName
  cases routeAB
  cases routeShared
  cases routeDyadic
  cases routeRegular
  cases routeSeal
  cases routeLedger
  cases routeName
  exact ⟨rfl, rfl⟩

theorem CofinalModulusNormalizationSeal_obligation_row_transport [AskSetup] [PackageSetup]
    {A B M W D R E H C P L N A' B' M' W' D' R' E' H' C' P' L' N' sharedRead
      dyadicRead regularRead sealRead ledgerRead namedRead sharedRead' dyadicRead'
      regularRead' sealRead' ledgerRead' namedRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] →
      cofinalModulusNormalizationSealFields
          (CofinalModulusNormalizationSealUp.mk A' B' M' W' D' R' E' H' C' P' L' N') =
        [A', B', M', W', D', R', E', H', C', P', L', N'] →
        hsame A A' →
          hsame B B' →
            hsame W W' →
              hsame D D' →
                hsame R R' →
                  hsame E E' →
                    hsame L L' →
                      hsame N N' →
                        Cont A B M →
                          Cont A' B' M' →
                            Cont M W sharedRead →
                              Cont M' W' sharedRead' →
                                Cont sharedRead D dyadicRead →
                                  Cont sharedRead' D' dyadicRead' →
                                    Cont dyadicRead R regularRead →
                                      Cont dyadicRead' R' regularRead' →
                                        Cont regularRead E sealRead →
                                          Cont regularRead' E' sealRead' →
                                            Cont sealRead L ledgerRead →
                                              Cont sealRead' L' ledgerRead' →
                                                Cont ledgerRead N namedRead →
                                                  Cont ledgerRead' N' namedRead' →
                                                    PkgSig bundle namedRead pkg →
                                                      PkgSig bundle namedRead' pkg →
                                                        hsame M M' ∧
                                                          hsame sharedRead sharedRead' ∧
                                                            hsame dyadicRead dyadicRead' ∧
                                                              hsame regularRead regularRead' ∧
                                                                hsame sealRead sealRead' ∧
                                                                  hsame ledgerRead ledgerRead' ∧
                                                                    hsame namedRead
                                                                      namedRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig
  intro _fieldsExact _fieldsExact' sameA sameB sameW sameD sameR sameE sameL sameN
    routeAB routeAB' routeShared routeShared' routeDyadic routeDyadic' routeRegular
    routeRegular' routeSeal routeSeal' routeLedger routeLedger' routeName routeName'
    _namedPkg _namedPkg'
  have sameM : hsame M M' :=
    cont_respects_hsame sameA sameB routeAB routeAB'
  have sameShared : hsame sharedRead sharedRead' :=
    cont_respects_hsame sameM sameW routeShared routeShared'
  have sameDyadic : hsame dyadicRead dyadicRead' :=
    cont_respects_hsame sameShared sameD routeDyadic routeDyadic'
  have sameRegular : hsame regularRead regularRead' :=
    cont_respects_hsame sameDyadic sameR routeRegular routeRegular'
  have sameSeal : hsame sealRead sealRead' :=
    cont_respects_hsame sameRegular sameE routeSeal routeSeal'
  have sameLedger : hsame ledgerRead ledgerRead' :=
    cont_respects_hsame sameSeal sameL routeLedger routeLedger'
  have sameNamed : hsame namedRead namedRead' :=
    cont_respects_hsame sameLedger sameN routeName routeName'
  exact
    ⟨sameM, sameShared, sameDyadic, sameRegular, sameSeal, sameLedger, sameNamed⟩

theorem CofinalModulusNormalizationSeal_obligation_scope [AskSetup] [PackageSetup]
    {A B M W D R E H C P L N A' B' M' W' D' R' E' H' C' P' L' N' sharedRead
      dyadicRead regularRead sealRead ledgerRead namedRead sharedRead' dyadicRead'
      regularRead' sealRead' ledgerRead' namedRead' scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalModulusNormalizationSealFields
        (CofinalModulusNormalizationSealUp.mk A B M W D R E H C P L N) =
      [A, B, M, W, D, R, E, H, C, P, L, N] →
      cofinalModulusNormalizationSealFields
          (CofinalModulusNormalizationSealUp.mk A' B' M' W' D' R' E' H' C' P' L' N') =
        [A', B', M', W', D', R', E', H', C', P', L', N'] →
        hsame A A' →
          hsame B B' →
            hsame W W' →
              hsame D D' →
                hsame R R' →
                  hsame E E' →
                    hsame L L' →
                      hsame N N' →
                        Cont A B M →
                          Cont A' B' M' →
                            Cont M W sharedRead →
                              Cont M' W' sharedRead' →
                                Cont sharedRead D dyadicRead →
                                  Cont sharedRead' D' dyadicRead' →
                                    Cont dyadicRead R regularRead →
                                      Cont dyadicRead' R' regularRead' →
                                        Cont regularRead E sealRead →
                                          Cont regularRead' E' sealRead' →
                                            Cont sealRead L ledgerRead →
                                              Cont sealRead' L' ledgerRead' →
                                                Cont ledgerRead N namedRead →
                                                  Cont ledgerRead' N' namedRead' →
                                                    Cont namedRead namedRead' scopedRead →
                                                      PkgSig bundle namedRead pkg →
                                                        PkgSig bundle namedRead' pkg →
                                                          hsame scopedRead
                                                              (append namedRead namedRead') ∧
                                                            hsame namedRead namedRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig
  intro fieldsExact fieldsExact' sameA sameB sameW sameD sameR sameE sameL sameN
    routeAB routeAB' routeShared routeShared' routeDyadic routeDyadic' routeRegular
    routeRegular' routeSeal routeSeal' routeLedger routeLedger' routeName routeName'
    scopedRoute namedPkg namedPkg'
  have transportedRows :=
    CofinalModulusNormalizationSeal_obligation_row_transport
      (bundle := bundle) (pkg := pkg)
      fieldsExact fieldsExact' sameA sameB sameW sameD sameR sameE sameL sameN
      routeAB routeAB' routeShared routeShared' routeDyadic routeDyadic' routeRegular
      routeRegular' routeSeal routeSeal' routeLedger routeLedger' routeName routeName'
      namedPkg namedPkg'
  cases scopedRoute
  exact ⟨hsame_refl (append namedRead namedRead'), transportedRows.right.right.right.right.right.right⟩

end BEDC.Derived.CofinalModulusNormalizationSealUp
