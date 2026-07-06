import BEDC.Derived.SubshiftUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubshiftUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubshiftCarrier_cantor_baire_handoff [AskSetup] [PackageSetup]
    {alphabet window language shift cantor baire _transport stream provenance nameCert cantorRead
      baireRead streamRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory alphabet ->
      UnaryHistory window ->
        UnaryHistory language ->
          UnaryHistory shift ->
            UnaryHistory cantor ->
              UnaryHistory baire ->
                UnaryHistory stream ->
                  Cont cantor window cantorRead ->
                    Cont baire window baireRead ->
                      Cont language shift streamRead ->
                        Cont streamRead stream provenance ->
                          PkgSig bundle provenance pkg ->
                            hsame provenance publicRead ->
                              hsame publicRead nameCert ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row streamRead ∧
                                      UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row alphabet ∨ hsame row window ∨
                                        hsame row language ∨ hsame row shift ∨
                                          hsame row cantor ∨ hsame row baire ∨
                                            hsame row cantorRead ∨ hsame row baireRead ∨
                                              hsame row streamRead ∨ hsame row provenance ∨
                                                hsame row nameCert)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont cantor window cantorRead ∧
                                        Cont baire window baireRead ∧
                                          Cont language shift streamRead ∧
                                            Cont streamRead stream provenance ∧
                                              PkgSig bundle provenance pkg)
                                    hsame ∧
                                  UnaryHistory cantorRead ∧ UnaryHistory baireRead ∧
                                    UnaryHistory streamRead ∧ UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro _alphabetUnary windowUnary languageUnary shiftUnary cantorUnary baireUnary streamUnary
    cantorWindow baireWindow languageShift streamRoute provenancePkg provenancePublic
    publicName
  have cantorReadUnary : UnaryHistory cantorRead :=
    unary_cont_closed cantorUnary windowUnary cantorWindow
  have baireReadUnary : UnaryHistory baireRead :=
    unary_cont_closed baireUnary windowUnary baireWindow
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed languageUnary shiftUnary languageShift
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed streamReadUnary streamUnary streamRoute
  have nameCertUnary : UnaryHistory nameCert :=
    unary_transport (unary_transport provenanceUnary provenancePublic) publicName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row streamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row alphabet ∨ hsame row window ∨ hsame row language ∨ hsame row shift ∨
              hsame row cantor ∨ hsame row baire ∨ hsame row cantorRead ∨
                hsame row baireRead ∨ hsame row streamRead ∨ hsame row provenance ∨
                  hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cantor window cantorRead ∧
              Cont baire window baireRead ∧ Cont language shift streamRead ∧
                Cont streamRead stream provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro streamRead ⟨hsame_refl streamRead, streamReadUnary⟩
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
                    (Or.inr (Or.inr (Or.inl source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cantorWindow, baireWindow, languageShift, streamRoute, provenancePkg⟩
  }
  exact ⟨cert, cantorReadUnary, baireReadUnary, streamReadUnary, nameCertUnary⟩

theorem SubshiftCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {alphabet window language shift cantor baire _transport stream provenance nameCert
      streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory alphabet →
      UnaryHistory window →
        UnaryHistory language →
          UnaryHistory shift →
            UnaryHistory cantor →
              UnaryHistory baire →
                UnaryHistory stream →
                  Cont language shift streamRead →
                    Cont streamRead stream provenance →
                      PkgSig bundle provenance pkg →
                        hsame provenance nameCert →
                          SemanticNameCert
                              (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row alphabet ∨ hsame row window ∨ hsame row language ∨
                                  hsame row shift ∨ hsame row cantor ∨ hsame row baire ∨
                                    hsame row streamRead ∨ hsame row provenance ∨
                                      hsame row nameCert)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont language shift streamRead ∧
                                  Cont streamRead stream provenance ∧
                                    PkgSig bundle provenance pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro alphabetUnary windowUnary languageUnary shiftUnary cantorUnary baireUnary streamUnary
    languageShift streamRoute provenancePkg provenanceName
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed languageUnary shiftUnary languageShift
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed streamReadUnary streamUnary streamRoute
  have nameCertUnary : UnaryHistory nameCert :=
    unary_transport provenanceUnary provenanceName
  exact {
    core := {
      carrier_inhabited := Exists.intro nameCert ⟨hsame_refl nameCert, nameCertUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, languageShift, streamRoute, provenancePkg⟩
  }

end BEDC.Derived.SubshiftUp
