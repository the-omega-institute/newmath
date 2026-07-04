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

theorem RegularCauchyTailSchedule_obligation_exhaustion [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe : BHist}
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
                      SemanticNameCert
                        (fun row : BHist => hsame row fe ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
                            hsame row K ∨ hsame row T ∨ hsame row M ∨ hsame row F ∨
                              hsame row E ∨ hsame row fe)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧
                            Cont rw D wd ∧ Cont wd K dk ∧ Cont dk T kt ∧
                              Cont kt M tm ∧ Cont tm F mf ∧ Cont mf E fe ∧
                                PkgSig bundle P pkg)
                        hsame ∧ UnaryHistory fe := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
  obtain ⟨qUnary, rUnary, wUnary, dUnary, kUnary, tUnary, mUnary, fUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _carrierQR, _carrierTail, _carrierMeet,
    _carrierSeal, provenancePkg, _namePkg⟩ := carrier
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fe ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
              hsame row K ∨ hsame row T ∨ hsame row M ∨ hsame row F ∨
                hsame row E ∨ hsame row fe)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧ Cont rw D wd ∧
              Cont wd K dk ∧ Cont dk T kt ∧ Cont kt M tm ∧ Cont tm F mf ∧
                Cont mf E fe ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fe ⟨hsame_refl fe, feUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeQR, routeRW, routeWD, routeDK, routeKT, routeTM, routeMF,
          routeFE, provenancePkg⟩
  }
  exact ⟨cert, feUnary⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
