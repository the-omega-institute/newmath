import BEDC.Derived.RegularCauchyTailScheduleUp.ObligationExhaustion

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailScheduleNameCertObligations [AskSetup] [PackageSetup]
    {Q R W D K T M F E H C P N qr rw wd dk kt tm mf fe namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier Q R W D K T M F E H C P N bundle pkg →
      Cont Q R qr →
        Cont qr W rw →
          Cont rw D wd →
            Cont wd K dk →
              Cont dk T kt →
                Cont kt M tm →
                  Cont tm F mf →
                    Cont mf E fe →
                      Cont fe N namedRead →
                        PkgSig bundle namedRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row Q ∨ hsame row R ∨ hsame row W ∨
                                  hsame row D ∨ hsame row K ∨ hsame row T ∨
                                    hsame row M ∨ hsame row F ∨ hsame row E ∨
                                      hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧
                                  Cont rw D wd ∧ Cont wd K dk ∧ Cont dk T kt ∧
                                    Cont kt M tm ∧ Cont tm F mf ∧ Cont mf E fe ∧
                                      Cont fe N namedRead ∧ PkgSig bundle P pkg ∧
                                        PkgSig bundle namedRead pkg)
                              hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier routeQR routeRW routeWD routeDK routeKT routeTM routeMF routeFE
    routeNamed namedReadPkg
  obtain ⟨qUnary, rUnary, wUnary, dUnary, kUnary, tUnary, mUnary, fUnary, eUnary,
    _hUnary, _cUnary, _pUnary, nUnary, _carrierQR, _carrierTail, _carrierMeet,
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
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed feUnary nUnary routeNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row R ∨ hsame row W ∨ hsame row D ∨
              hsame row K ∨ hsame row T ∨ hsame row M ∨ hsame row F ∨
                hsame row E ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q R qr ∧ Cont qr W rw ∧ Cont rw D wd ∧
              Cont wd K dk ∧ Cont dk T kt ∧ Cont kt M tm ∧ Cont tm F mf ∧
                Cont mf E fe ∧ Cont fe N namedRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨namedRead, ⟨hsame_refl namedRead, namedReadUnary⟩⟩
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
          routeFE, routeNamed, provenancePkg, namedReadPkg⟩
  }
  exact ⟨cert, namedReadUnary⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
