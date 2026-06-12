import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FrechetFilterCarrier [AskSetup] [PackageSetup]
    (U T S M B Q R A H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory U ∧ UnaryHistory T ∧ UnaryHistory S ∧ UnaryHistory M ∧
    UnaryHistory B ∧ UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory A ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont U T S ∧ Cont S M B ∧ Cont B Q R ∧ Cont R A C ∧
          PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem FrechetFilterRootCauchyConsumerBoundary [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N cauchyRead readbackRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      Cont U T cauchyRead ->
        Cont cauchyRead Q readbackRead ->
          Cont readbackRead R sealRead ->
            Cont sealRead N namedRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
                          hsame row B ∨ hsame row Q ∨ hsame row R ∨ hsame row A ∨
                            hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont U T cauchyRead ∧
                          Cont cauchyRead Q readbackRead ∧ Cont readbackRead R sealRead ∧
                            Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier cauchyRoute readbackRoute sealRoute nameRoute provenancePkg namedPkg
  obtain ⟨UUnary, TUnary, _SUnary, _MUnary, _BUnary, QUnary, RUnary, _AUnary,
    _HUnary, _CUnary, _PUnary, NUnary, _carrierRootRoute, _carrierScheduleRoute,
    _carrierReadbackRoute, _carrierSealRoute, _carrierProvenancePkg, _carrierNamePkg⟩ :=
      carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed UUnary TUnary cauchyRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyUnary QUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary RUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary NUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨ hsame row B ∨
              hsame row Q ∨ hsame row R ∨ hsame row A ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U T cauchyRead ∧ Cont cauchyRead Q readbackRead ∧
              Cont readbackRead R sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, cauchyRoute, readbackRoute, sealRoute, nameRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

theorem FrechetFilterRootTailBaseAdmission [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N tailWindow scheduled metricMeet namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      Cont U T tailWindow ->
        Cont tailWindow S scheduled ->
          Cont scheduled B metricMeet ->
            Cont metricMeet N namedRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
                          hsame row B ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont U T tailWindow ∧
                          Cont tailWindow S scheduled ∧ Cont scheduled B metricMeet ∧
                            Cont metricMeet N namedRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute scheduleRoute meetRoute nameRoute provenancePkg namedPkg
  obtain ⟨UUnary, TUnary, SUnary, _MUnary, BUnary, _QUnary, _RUnary, _AUnary,
    _HUnary, _CUnary, _PUnary, NUnary, _carrierRootRoute, _carrierScheduleRoute,
    _carrierReadbackRoute, _carrierSealRoute, _carrierProvenancePkg, _carrierNamePkg⟩ :=
      carrier
  have tailUnary : UnaryHistory tailWindow :=
    unary_cont_closed UUnary TUnary tailRoute
  have scheduledUnary : UnaryHistory scheduled :=
    unary_cont_closed tailUnary SUnary scheduleRoute
  have metricMeetUnary : UnaryHistory metricMeet :=
    unary_cont_closed scheduledUnary BUnary meetRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed metricMeetUnary NUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
              hsame row B ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U T tailWindow ∧ Cont tailWindow S scheduled ∧
              Cont scheduled B metricMeet ∧ Cont metricMeet N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, tailRoute, scheduleRoute, meetRoute, nameRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

theorem FrechetFilterConvergenceConsumerHandoffObligation [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N tailRead scheduleRead filterRead cauchyRead readbackRead
      sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      Cont U T tailRead ->
        Cont tailRead S scheduleRead ->
          Cont scheduleRead B filterRead ->
            Cont filterRead Q cauchyRead ->
              Cont cauchyRead R readbackRead ->
                Cont readbackRead A sealRead ->
                  Cont sealRead N namedRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle namedRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
                                hsame row B ∨ hsame row Q ∨ hsame row R ∨ hsame row A ∨
                                  hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont U T tailRead ∧
                                Cont tailRead S scheduleRead ∧
                                  Cont scheduleRead B filterRead ∧
                                    Cont filterRead Q cauchyRead ∧
                                      Cont cauchyRead R readbackRead ∧
                                        Cont readbackRead A sealRead ∧
                                          Cont sealRead N namedRead ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle namedRead pkg)
                            hsame ∧
                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute scheduleRoute filterRoute cauchyRoute readbackRoute sealRoute
    nameRoute provenancePkg namedPkg
  obtain ⟨UUnary, TUnary, SUnary, _MUnary, BUnary, QUnary, RUnary, AUnary,
    _HUnary, _CUnary, _PUnary, NUnary, _carrierRootRoute, _carrierScheduleRoute,
    _carrierReadbackRoute, _carrierSealRoute, _carrierProvenancePkg, _carrierNamePkg⟩ :=
      carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed UUnary TUnary tailRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed tailUnary SUnary scheduleRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed scheduleUnary BUnary filterRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed filterUnary QUnary cauchyRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyUnary RUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary AUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary NUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨ hsame row B ∨
              hsame row Q ∨ hsame row R ∨ hsame row A ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U T tailRead ∧ Cont tailRead S scheduleRead ∧
              Cont scheduleRead B filterRead ∧ Cont filterRead Q cauchyRead ∧
                Cont cauchyRead R readbackRead ∧ Cont readbackRead A sealRead ∧
                  Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, tailRoute, scheduleRoute, filterRoute, cauchyRoute, readbackRoute,
          sealRoute, nameRoute, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, namedUnary⟩

theorem FrechetFilterCompletionNonescape [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N sourceRead cauchyRead readbackRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FrechetFilterCarrier U T S M B Q R A H C P N bundle pkg ->
      Cont U T sourceRead ->
        Cont sourceRead Q cauchyRead ->
          Cont cauchyRead R readbackRead ->
            Cont readbackRead N completionRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle completionRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row U ∨ hsame row T ∨ hsame row Q ∨ hsame row R ∨
                        hsame row N ∨ hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont U T sourceRead ∧
                        Cont sourceRead Q cauchyRead ∧ Cont cauchyRead R readbackRead ∧
                          Cont readbackRead N completionRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle completionRead pkg)
                    hsame ∧
                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sourceRoute cauchyRoute readbackRoute completionRoute provenancePkg
    completionPkg
  obtain ⟨UUnary, TUnary, _SUnary, _MUnary, _BUnary, QUnary, RUnary, _AUnary,
    _HUnary, _CUnary, _PUnary, NUnary, _carrierTailRoute, _carrierScheduleRoute,
    _carrierCauchyRoute, _carrierReadbackRoute, _carrierProvenancePkg,
    _carrierNamePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed UUnary TUnary sourceRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed sourceUnary QUnary cauchyRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed cauchyUnary RUnary readbackRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed readbackUnary NUnary completionRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row U ∨ hsame row T ∨ hsame row Q ∨ hsame row R ∨ hsame row N ∨
            hsame row completionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont U T sourceRead ∧ Cont sourceRead Q cauchyRead ∧
            Cont cauchyRead R readbackRead ∧ Cont readbackRead N completionRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg)
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, sourceRoute, cauchyRoute, readbackRoute, completionRoute,
          provenancePkg, completionPkg⟩
  }
  exact ⟨cert, completionUnary⟩

end BEDC.Derived.FrechetFilterUp
