import BEDC.Derived.RegularCauchyTailScheduleUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_bridge_route [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory R ->
        UnaryHistory W ->
          UnaryHistory D ->
            UnaryHistory K ->
              UnaryHistory T ->
                UnaryHistory M ->
                  UnaryHistory F ->
                    UnaryHistory E ->
                      Cont Q R qr ->
                        Cont qr W rw ->
                          Cont rw D wd ->
                            Cont wd K dk ->
                              Cont dk T kt ->
                                Cont kt M tm ->
                                  Cont tm F mf ->
                                    Cont mf E fe ->
                                      PkgSig bundle P pkg ->
                                        PkgSig bundle sealedRead pkg ->
                                          hsame kt (append dk T) ∧
                                            hsame fe (append mf E) ∧
                                              UnaryHistory qr ∧
                                                UnaryHistory rw ∧
                                                  UnaryHistory wd ∧
                                                    UnaryHistory dk ∧
                                                      UnaryHistory kt ∧
                                                        UnaryHistory tm ∧
                                                          UnaryHistory mf ∧
                                                            UnaryHistory fe ∧
                                                              regularCauchyTailScheduleFromEventFlow
                                                                  (regularCauchyTailScheduleToEventFlow
                                                                    (RegularCauchyTailScheduleUp.mk
                                                                      Q R W D K T M F E H C P N)) =
                                                                some
                                                                  (RegularCauchyTailScheduleUp.mk
                                                                    Q R W D K T M F E H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark Cont PkgSig UnaryHistory hsame
  intro unaryQ unaryR unaryW unaryD unaryK unaryT unaryM unaryF unaryE
    routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE _pkgP _pkgSealed
  have unaryQR : UnaryHistory qr :=
    unary_cont_closed unaryQ unaryR routeQR
  have unaryRW : UnaryHistory rw :=
    unary_cont_closed unaryQR unaryW routeRW
  have unaryWD : UnaryHistory wd :=
    unary_cont_closed unaryRW unaryD routeWD
  have unaryDK : UnaryHistory dk :=
    unary_cont_closed unaryWD unaryK routeDK
  have unaryKT : UnaryHistory kt :=
    unary_cont_closed unaryDK unaryT routeKT
  have unaryTM : UnaryHistory tm :=
    unary_cont_closed unaryKT unaryM routeTM
  have unaryMF : UnaryHistory mf :=
    unary_cont_closed unaryTM unaryF routeMF
  have unaryFE : UnaryHistory fe :=
    unary_cont_closed unaryMF unaryE routeFE
  exact
    ⟨routeKT, routeFE, unaryQR, unaryRW, unaryWD, unaryDK, unaryKT, unaryTM, unaryMF,
      unaryFE,
      RegularCauchyTailScheduleTasteGate_single_carrier_alignment.2.1
        (RegularCauchyTailScheduleUp.mk Q R W D K T M F E H C P N)⟩

theorem RegularCauchyTailSchedule_tail_route_totality [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier Q R W D K T M F E H C P N bundle pkg ->
      Cont Q R qr ->
        Cont qr W rw ->
          Cont rw D wd ->
            Cont wd K dk ->
              Cont dk T kt ->
                Cont kt M tm ->
                  Cont tm F mf ->
                    Cont mf E fe ->
                      PkgSig bundle sealedRead pkg ->
                        UnaryHistory qr ∧
                          UnaryHistory rw ∧
                            UnaryHistory wd ∧
                              UnaryHistory dk ∧
                                UnaryHistory kt ∧
                                  UnaryHistory tm ∧
                                    UnaryHistory mf ∧
                                      UnaryHistory fe ∧
                                        hsame kt (append dk T) ∧
                                          hsame fe (append mf E) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame UnaryHistory
  intro carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE _sealedPkg
  obtain ⟨qUnary, rUnary, wUnary, dUnary, kUnary, tUnary, mUnary, fUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _carrierQR, _carrierTail, _carrierMeet,
    _carrierSeal, _provenancePkg, _namePkg⟩ := carrier
  have qrUnary : UnaryHistory qr :=
    unary_cont_closed qUnary rUnary routeQR
  have rwUnary : UnaryHistory rw :=
    unary_cont_closed qrUnary wUnary routeRW
  have wdUnary : UnaryHistory wd :=
    unary_cont_closed rwUnary dUnary routeWD
  have dkUnary : UnaryHistory dk :=
    unary_cont_closed wdUnary kUnary routeDK
  have ktUnary : UnaryHistory kt :=
    unary_cont_closed dkUnary tUnary routeKT
  have tmUnary : UnaryHistory tm :=
    unary_cont_closed ktUnary mUnary routeTM
  have mfUnary : UnaryHistory mf :=
    unary_cont_closed tmUnary fUnary routeMF
  have feUnary : UnaryHistory fe :=
    unary_cont_closed mfUnary eUnary routeFE
  exact
    ⟨qrUnary, rwUnary, wdUnary, dkUnary, ktUnary, tmUnary, mfUnary, feUnary,
      routeKT, routeFE⟩

theorem RegularCauchyTailSchedule_real_completion_scope [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier Q R W D K T M F E H C P N bundle pkg ->
      Cont Q R qr ->
        Cont qr W rw ->
          Cont rw D wd ->
            Cont wd K dk ->
              Cont dk T kt ->
                Cont kt M tm ->
                  Cont tm F mf ->
                    Cont mf E fe ->
                      Cont fe H realRead ->
                        PkgSig bundle realRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
                                  hsame row K ∨ hsame row T ∨ hsame row M ∨
                                    hsame row F ∨ hsame row E ∨ hsame row realRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧
                                  Cont rw D wd ∧ Cont wd K dk ∧ Cont dk T kt ∧
                                    Cont kt M tm ∧ Cont tm F mf ∧ Cont mf E fe ∧
                                      Cont fe H realRead ∧ PkgSig bundle realRead pkg)
                              hsame ∧ UnaryHistory qr ∧ UnaryHistory rw ∧
                            UnaryHistory wd ∧ UnaryHistory dk ∧ UnaryHistory kt ∧
                              UnaryHistory tm ∧ UnaryHistory mf ∧ UnaryHistory fe ∧
                                UnaryHistory realRead ∧ hsame kt (append dk T) ∧
                                  hsame fe (append mf E) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
    realReadRoute realReadPkg
  obtain ⟨qUnary, rUnary, wUnary, dUnary, kUnary, tUnary, mUnary, fUnary, eUnary,
    hUnary, _cUnary, _pUnary, _nUnary, _carrierQR, _carrierTail, _carrierMeet,
    _carrierSeal, _provenancePkg, _namePkg⟩ := carrier
  have qrUnary : UnaryHistory qr :=
    unary_cont_closed qUnary rUnary routeQR
  have rwUnary : UnaryHistory rw :=
    unary_cont_closed qrUnary wUnary routeRW
  have wdUnary : UnaryHistory wd :=
    unary_cont_closed rwUnary dUnary routeWD
  have dkUnary : UnaryHistory dk :=
    unary_cont_closed wdUnary kUnary routeDK
  have ktUnary : UnaryHistory kt :=
    unary_cont_closed dkUnary tUnary routeKT
  have tmUnary : UnaryHistory tm :=
    unary_cont_closed ktUnary mUnary routeTM
  have mfUnary : UnaryHistory mf :=
    unary_cont_closed tmUnary fUnary routeMF
  have feUnary : UnaryHistory fe :=
    unary_cont_closed mfUnary eUnary routeFE
  have ktReadback : hsame kt (append dk T) :=
    routeKT
  have feReadback : hsame fe (append mf E) :=
    routeFE
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed feUnary hUnary realReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
              hsame row K ∨ hsame row T ∨ hsame row M ∨
                hsame row F ∨ hsame row E ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧ Cont rw D wd ∧
              Cont wd K dk ∧ Cont dk T kt ∧ Cont kt M tm ∧ Cont tm F mf ∧
                Cont mf E fe ∧ Cont fe H realRead ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeQR, routeRW, routeWD, routeDK, routeKT, routeTM, routeMF,
          routeFE, realReadRoute, realReadPkg⟩
  }
  exact
    ⟨cert, qrUnary, rwUnary, wdUnary, dkUnary, ktUnary, tmUnary, mfUnary, feUnary,
      realReadUnary, ktReadback, feReadback⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
