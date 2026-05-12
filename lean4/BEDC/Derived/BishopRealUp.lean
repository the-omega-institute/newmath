import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRealPacket_standard_finite_packet_bridge [AskSetup] [PackageSetup]
    {schedule regular endpoint modulus located apart sealRow transport route provenance ledger
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory schedule ->
      UnaryHistory regular ->
        UnaryHistory endpoint ->
          UnaryHistory modulus ->
            UnaryHistory located ->
              UnaryHistory apart ->
                UnaryHistory sealRow ->
                  UnaryHistory transport ->
                    UnaryHistory route ->
                      UnaryHistory provenance ->
                        UnaryHistory ledger ->
                          Cont schedule regular endpoint ->
                            Cont endpoint modulus sealRow ->
                              Cont located apart bridge ->
                                Cont route sealRow ledger ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle ledger pkg ->
                                      PkgSig bundle bridge pkg ->
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row bridge ∧ UnaryHistory row ∧
                                              Cont located apart row ∧ PkgSig bundle row pkg)
                                          (fun row : BHist =>
                                            UnaryHistory schedule ∧ UnaryHistory regular ∧
                                              UnaryHistory endpoint ∧ UnaryHistory modulus ∧
                                                UnaryHistory located ∧ UnaryHistory apart ∧
                                                  UnaryHistory sealRow ∧
                                                    Cont schedule regular endpoint ∧
                                                      Cont endpoint modulus sealRow ∧
                                                        Cont located apart row)
                                          (fun row : BHist =>
                                            PkgSig bundle row pkg ∧ PkgSig bundle ledger pkg ∧
                                              Cont route sealRow ledger)
                                          (fun row row' : BHist =>
                                            psame bundle pkg pkg ∧ hsame row row') := by
  intro scheduleUnary regularUnary endpointUnary modulusUnary locatedUnary apartUnary sealRowUnary
    _transportUnary _routeUnary _provenanceUnary _ledgerUnary scheduleRegularEndpoint
    endpointModulusSeal locatedApartBridge routeSealLedger _provenancePkg ledgerPkg bridgePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridge ⟨hsame_refl bridge, unary_cont_closed locatedUnary apartUnary
          locatedApartBridge, locatedApartBridge, bridgePkg⟩
      equiv_refl := by
        intro row sourceRow
        exact ⟨PkgSig_psame_intro sourceRow.right.right.right sourceRow.right.right.right
          (hsame_refl row), hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        exact ⟨classified.left, hsame_symm classified.right⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left, hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨scheduleUnary, regularUnary, endpointUnary, modulusUnary, locatedUnary, apartUnary,
          sealRowUnary, scheduleRegularEndpoint, endpointModulusSeal, sourceRow.right.right.left⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right.right, ledgerPkg, routeSealLedger⟩
  }

end BEDC.Derived.BishopRealUp
