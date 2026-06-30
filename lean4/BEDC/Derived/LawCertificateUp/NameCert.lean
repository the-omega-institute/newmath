import BEDC.Derived.LawCertificateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.LawCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem LawCertificate_semantic_name_certificate [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
        [F, P, C, S, E, Ld, H, R, Q, N] →
      Cont F P C →
        Cont S E Ld →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row C ∧
                  ∃ packet : LawCertificateUp,
                    packet = LawCertificateUp.mk F P C S E Ld H R Q N ∧
                      lawCertificateFields packet = [F, P, C, S, E, Ld, H, R, Q, N])
              (fun row : BHist => Cont F P row ∧ Cont S E Ld)
              (fun row : BHist => hsame row C ∧ PkgSig bundle N pkg ∧ hsame H H)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact sourcePatternClassifier stabilityFailureLedger packageName
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨C, hsame_refl C,
            LawCertificateUp.mk F P C S E Ld H R Q N, rfl, fieldsExact⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨sourcePatternClassifier, stabilityFailureLedger⟩
    ledger_sound := by
      intro row source
      exact ⟨source.left, packageName, hsame_refl H⟩
  }

theorem LawCertificateCarrier_carrier_admission [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N routed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
        [F, P, C, S, E, Ld, H, R, Q, N] →
      Cont F P C →
        Cont S E Ld →
          Cont H R routed →
            PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row C ∧
                      ∃ packet : LawCertificateUp,
                        packet = LawCertificateUp.mk F P C S E Ld H R Q N ∧
                          lawCertificateFields packet = [F, P, C, S, E, Ld, H, R, Q, N])
                  (fun row : BHist => Cont F P row ∧ Cont S E Ld)
                  (fun row : BHist => hsame row C ∧ Cont H R routed ∧ PkgSig bundle N pkg)
                  hsame ∧
                Cont F P C ∧ Cont S E Ld ∧ Cont H R routed := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro fieldsExact sourceClassifier stabilityLedger routedReplay packageName
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨C, hsame_refl C,
              LawCertificateUp.mk F P C S E Ld H R Q N, rfl, fieldsExact⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          cases sameRows
          exact source
      }
      pattern_sound := by
        intro row source
        cases source.left
        exact ⟨sourceClassifier, stabilityLedger⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, routedReplay, packageName⟩
    }
  · exact ⟨sourceClassifier, stabilityLedger, routedReplay⟩

theorem LawCertificateCarrier_bridge_carrier_route [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N transported publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateClassifier (LawCertificateUp.mk F P C S E Ld H R Q N)
        (LawCertificateUp.mk F P C S E Ld H R Q N) →
      Cont H R transported →
        Cont transported N publicRead →
          PkgSig bundle N pkg →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row publicRead ∧
                      lawCertificateClassifier (LawCertificateUp.mk F P C S E Ld H R Q N)
                        (LawCertificateUp.mk F P C S E Ld H R Q N))
                  (fun row : BHist => Cont H R transported ∧ Cont transported N row)
                  (fun row : BHist =>
                    hsame row publicRead ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle publicRead pkg)
                  hsame ∧
                Cont H R transported ∧ Cont transported N publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro classifierSelf transportedRoute publicRoute packageName packagePublic
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact ⟨publicRead, hsame_refl publicRead, classifierSelf⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨transportedRoute,
            cont_result_hsame_transport publicRoute (hsame_symm source.left)⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, packageName, packagePublic⟩
    }
  · exact ⟨transportedRoute, publicRoute⟩

end BEDC.Derived.LawCertificateUp
