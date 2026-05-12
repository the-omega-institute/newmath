import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFamilyCarrier_modulus_window_exactness [AskSetup] [PackageSetup]
    {memberLedger memberRow modulus streamWindow dyadicLedger diagonalRoute provenance
      localCert selectedMember selectedWindow observation completionRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory memberLedger ->
      UnaryHistory memberRow ->
        UnaryHistory modulus ->
          UnaryHistory streamWindow ->
            UnaryHistory dyadicLedger ->
              UnaryHistory diagonalRoute ->
                Cont modulus memberRow selectedMember ->
                  Cont selectedMember streamWindow selectedWindow ->
                    Cont selectedWindow dyadicLedger observation ->
                      Cont observation diagonalRoute completionRoute ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle localCert pkg ->
                            PkgSig bundle completionRoute pkg ->
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row completionRoute ∧ UnaryHistory row ∧
                                    PkgSig bundle row pkg)
                                (fun row : BHist =>
                                  Cont observation diagonalRoute row ∧ PkgSig bundle row pkg)
                                (fun _row : BHist =>
                                  UnaryHistory memberLedger ∧ UnaryHistory modulus ∧
                                    UnaryHistory streamWindow ∧ UnaryHistory dyadicLedger ∧
                                      UnaryHistory diagonalRoute ∧
                                        Cont modulus memberRow selectedMember ∧
                                          Cont selectedMember streamWindow selectedWindow ∧
                                            Cont selectedWindow dyadicLedger observation ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle localCert pkg)
                                hsame := by
  intro memberLedgerUnary memberRowUnary modulusUnary streamWindowUnary dyadicLedgerUnary
  intro diagonalRouteUnary modulusMemberSelected selectedMemberWindow selectedWindowLedger
  intro observationDiagonalCompletion provenancePkg localCertPkg completionRoutePkg
  have selectedMemberUnary : UnaryHistory selectedMember :=
    unary_cont_closed modulusUnary memberRowUnary modulusMemberSelected
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed selectedMemberUnary streamWindowUnary selectedMemberWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed selectedWindowUnary dyadicLedgerUnary selectedWindowLedger
  have completionRouteUnary : UnaryHistory completionRoute :=
    unary_cont_closed observationUnary diagonalRouteUnary observationDiagonalCompletion
  have sourceCompletion :
      hsame completionRoute completionRoute ∧ UnaryHistory completionRoute ∧
        PkgSig bundle completionRoute pkg :=
    ⟨hsame_refl completionRoute, completionRouteUnary, completionRoutePkg⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro completionRoute sourceCompletion
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro row row' classified sourceRow
        exact
          ⟨hsame_trans (hsame_symm classified) sourceRow.left,
            unary_transport sourceRow.right.left classified,
            by
              cases classified
              exact sourceRow.right.right⟩
    }
    pattern_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨observationDiagonalCompletion, sourceRow.right.right⟩
    ledger_sound := by
      intro _row _sourceRow
      exact
        ⟨memberLedgerUnary, modulusUnary, streamWindowUnary, dyadicLedgerUnary,
          diagonalRouteUnary, modulusMemberSelected, selectedMemberWindow,
          selectedWindowLedger, provenancePkg, localCertPkg⟩
  }

end BEDC.Derived.RegularCauchyFamilyUp
