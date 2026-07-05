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

theorem RegularCauchyTailSchedule_public_consumer_surface [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe completionRead : BHist}
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
                      Cont fe H completionRead ->
                        PkgSig bundle completionRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
                                  hsame row K ∨ hsame row T ∨ hsame row M ∨
                                    hsame row F ∨ hsame row E ∨ hsame row completionRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧
                                  Cont rw D wd ∧ Cont wd K dk ∧ Cont dk T kt ∧
                                    Cont kt M tm ∧ Cont tm F mf ∧ Cont mf E fe ∧
                                      Cont fe H completionRead ∧
                                        PkgSig bundle completionRead pkg)
                              hsame ∧ UnaryHistory qr ∧ UnaryHistory rw ∧
                            UnaryHistory wd ∧ UnaryHistory dk ∧ UnaryHistory kt ∧
                              UnaryHistory tm ∧ UnaryHistory mf ∧ UnaryHistory fe ∧
                                UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
    completionRoute completionPkg
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
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed feUnary hUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row K ∨
              hsame row T ∨ hsame row M ∨ hsame row F ∨ hsame row E ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧ Cont rw D wd ∧
              Cont wd K dk ∧ Cont dk T kt ∧ Cont kt M tm ∧ Cont tm F mf ∧
                Cont mf E fe ∧ Cont fe H completionRead ∧
                  PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
          routeFE, completionRoute, completionPkg⟩
  }
  exact
    ⟨cert, qrUnary, rwUnary, wdUnary, dkUnary, ktUnary, tmUnary, mfUnary, feUnary,
      completionUnary⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
