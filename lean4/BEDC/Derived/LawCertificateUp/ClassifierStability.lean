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

theorem LawCertificateCarrier_classifier_stability [AskSetup] [PackageSetup]
    {F P C S E Ld H R Q N row row' routed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawCertificateFields (LawCertificateUp.mk F P C S E Ld H R Q N) =
        [F, P, C, S, E, Ld, H, R, Q, N] →
      hsame row C →
        hsame row' C →
          Cont S E Ld →
            Cont H R routed →
              PkgSig bundle N pkg →
                SemanticNameCert
                    (fun x : BHist =>
                      hsame x C ∧
                        ∃ packet : LawCertificateUp,
                          packet = LawCertificateUp.mk F P C S E Ld H R Q N ∧
                            lawCertificateFields packet = [F, P, C, S, E, Ld, H, R, Q, N])
                    (fun x : BHist => Cont S E Ld ∧ hsame x row)
                    (fun x : BHist => hsame x C ∧ Cont H R routed ∧ PkgSig bundle N pkg)
                    hsame ∧
                  hsame row row' := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro fieldsExact rowClassifier row'Classifier stabilityRoute routedRoute packageName
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨C, hsame_refl C,
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
            hsame_trans source.left (hsame_symm rowClassifier)⟩
      ledger_sound := by
        intro x source
        exact ⟨source.left, routedRoute, packageName⟩
    }
  · exact hsame_trans rowClassifier (hsame_symm row'Classifier)

end BEDC.Derived.LawCertificateUp
