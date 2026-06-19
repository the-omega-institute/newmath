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

theorem LawCertificateCarrier_scope_transport [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N stabilityRead scopedRead transported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
        [F, P, C, S, E, Ld, H, R, Q, N] →
      Cont F P C →
        Cont S E stabilityRead →
          Cont stabilityRead Ld scopedRead →
            Cont H R transported →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun x : BHist =>
                      hsame x scopedRead ∧
                        ∃ packet : LawCertificateUp,
                          packet = LawCertificateUp.mk F P C S E Ld H R Q N ∧
                            lawCertificateFields packet = [F, P, C, S, E, Ld, H, R, Q, N])
                    (fun x : BHist => Cont S E stabilityRead ∧ Cont stabilityRead Ld x)
                    (fun x : BHist =>
                      hsame x scopedRead ∧ Cont H R transported ∧ PkgSig bundle N pkg)
                    hsame ∧
                  Cont H R transported := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro fieldsExact _sourceClassifier stabilityRoute scopedRoute transportedRoute packageName
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨scopedRead, hsame_refl scopedRead,
              LawCertificateUp.mk F P C S E Ld H R Q N, rfl, fieldsExact⟩
        equiv_refl := by
          intro x _source
          exact hsame_refl x
        equiv_symm := by
          intro _x _y sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _x _y _z sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro x y sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              source.right⟩
      }
      pattern_sound := by
        intro x source
        exact
          ⟨stabilityRoute,
            cont_result_hsame_transport scopedRoute (hsame_symm source.left)⟩
      ledger_sound := by
        intro x source
        exact ⟨source.left, transportedRoute, packageName⟩
    }
  · exact transportedRoute

theorem LawCertificateCarrier_public_export_route [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N stabilityRead scopedRead transported publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
        [F, P, C, S, E, Ld, H, R, Q, N] →
      Cont F P C →
        Cont S E stabilityRead →
          Cont stabilityRead Ld scopedRead →
            Cont H R transported →
              Cont transported N publicRead →
                PkgSig bundle N pkg →
                  PkgSig bundle publicRead pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row publicRead ∧
                            ∃ packet : LawCertificateUp,
                              packet = LawCertificateUp.mk F P C S E Ld H R Q N ∧
                                lawCertificateFields packet = [F, P, C, S, E, Ld, H, R, Q, N])
                        (fun row : BHist =>
                          Cont F P C ∧ Cont S E stabilityRead ∧
                            Cont stabilityRead Ld scopedRead ∧ Cont transported N row)
                        (fun row : BHist =>
                          hsame row publicRead ∧ Cont H R transported ∧
                            PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg)
                        hsame ∧
                      Cont transported N publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact sourceClassifier stabilityRoute scopedRoute transportedRoute publicRoute
    packageName packagePublic
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨publicRead, hsame_refl publicRead,
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
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨sourceClassifier, stabilityRoute, scopedRoute,
            cont_result_hsame_transport publicRoute (hsame_symm source.left)⟩
      ledger_sound := by
        intro row source
        exact
          ⟨source.left, transportedRoute, packageName, packagePublic⟩
    }
  · exact publicRoute

end BEDC.Derived.LawCertificateUp
