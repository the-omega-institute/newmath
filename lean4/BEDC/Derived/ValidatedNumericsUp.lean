import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ValidatedNumericsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ValidatedNumericsReadbackPacket_real_readback_soundness [AskSetup] [PackageSetup]
    {interval precision modulus observation readback containment provenance name finiteRead
      sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory precision ->
        UnaryHistory modulus ->
          UnaryHistory observation ->
            UnaryHistory readback ->
              UnaryHistory containment ->
                UnaryHistory provenance ->
                  UnaryHistory name ->
                    Cont modulus precision observation ->
                      Cont observation readback finiteRead ->
                        Cont interval containment sealRow ->
                          PkgSig bundle name pkg ->
                            PkgSig bundle sealRow pkg ->
                              UnaryHistory finiteRead ∧
                                UnaryHistory sealRow ∧
                                  Cont modulus precision observation ∧
                                    Cont observation readback finiteRead ∧
                                      Cont interval containment sealRow ∧
                                        PkgSig bundle name pkg ∧
                                          PkgSig bundle sealRow pkg := by
  intro intervalUnary _precisionUnary _modulusUnary observationUnary readbackUnary containmentUnary
  intro _provenanceUnary _nameUnary modulusPrecision observationReadback intervalContainment
  intro namePkg sealPkg
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed observationUnary readbackUnary observationReadback
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed intervalUnary containmentUnary intervalContainment
  exact ⟨finiteReadUnary, sealRowUnary, modulusPrecision, observationReadback, intervalContainment,
    namePkg, sealPkg⟩

theorem ValidatedNumericsReadbackPacket_precision_refinement_containment [AskSetup] [PackageSetup]
    {interval precision modulus observation readback containment provenance name refinedPrecision
      refinedObservation refinedContainment refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory precision ->
        UnaryHistory modulus ->
          UnaryHistory observation ->
            UnaryHistory readback ->
              UnaryHistory containment ->
                UnaryHistory provenance ->
                  UnaryHistory name ->
                    hsame precision refinedPrecision ->
                      hsame observation refinedObservation ->
                        Cont modulus refinedPrecision refinedObservation ->
                          Cont refinedObservation readback refinedRead ->
                            Cont interval containment refinedContainment ->
                              PkgSig bundle refinedContainment pkg ->
                                UnaryHistory refinedPrecision ∧ UnaryHistory refinedObservation ∧
                                  UnaryHistory refinedRead ∧ UnaryHistory refinedContainment ∧
                                    Cont modulus refinedPrecision refinedObservation ∧
                                      Cont refinedObservation readback refinedRead ∧
                                        Cont interval containment refinedContainment ∧
                                          PkgSig bundle refinedContainment pkg := by
  intro intervalUnary precisionUnary _modulusUnary observationUnary readbackUnary containmentUnary
  intro _provenanceUnary _nameUnary samePrecision sameObservation modulusPrecisionObservation
  intro observationReadback intervalContainment containmentPkg
  have refinedPrecisionUnary : UnaryHistory refinedPrecision :=
    unary_transport precisionUnary samePrecision
  have refinedObservationUnary : UnaryHistory refinedObservation :=
    unary_transport observationUnary sameObservation
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed refinedObservationUnary readbackUnary observationReadback
  have refinedContainmentUnary : UnaryHistory refinedContainment :=
    unary_cont_closed intervalUnary containmentUnary intervalContainment
  exact
    ⟨refinedPrecisionUnary, refinedObservationUnary, refinedReadUnary, refinedContainmentUnary,
      modulusPrecisionObservation, observationReadback, intervalContainment, containmentPkg⟩

theorem ValidatedNumericsFiniteEnclosure_exported_bridge [AskSetup] [PackageSetup]
    {interval endpoint precision modulus observation readback containment transport provenance name
      bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory interval ->
      UnaryHistory endpoint ->
        UnaryHistory precision ->
          UnaryHistory modulus ->
            UnaryHistory observation ->
              UnaryHistory readback ->
                UnaryHistory containment ->
                  UnaryHistory transport ->
                    UnaryHistory provenance ->
                      UnaryHistory name ->
                        Cont precision modulus observation ->
                          Cont observation readback containment ->
                            Cont containment provenance bridge ->
                              PkgSig bundle name pkg ->
                                PkgSig bundle bridge pkg ->
                                  SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row bridge ∧ UnaryHistory row ∧
                                        PkgSig bundle row pkg)
                                    (fun row : BHist =>
                                      UnaryHistory interval ∧ UnaryHistory endpoint ∧
                                        UnaryHistory precision ∧
                                          Cont containment provenance row)
                                    (fun row : BHist =>
                                      PkgSig bundle row pkg ∧
                                        Cont observation readback containment)
                                    (fun row row' : BHist =>
                                      PkgSig bundle row pkg ∧ hsame row row') := by
  intro intervalUnary endpointUnary precisionUnary _modulusUnary _observationUnary
  intro _readbackUnary containmentUnary _transportUnary provenanceUnary _nameUnary
  intro _precisionModulusObservation observationReadbackContainment containmentProvenanceBridge
  intro _namePkg bridgePkg
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed containmentUnary provenanceUnary containmentProvenanceBridge
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridge ⟨hsame_refl bridge, bridgeUnary, bridgePkg⟩
      equiv_refl := by
        intro row sourceRow
        exact ⟨sourceRow.right.right, hsame_refl row⟩
      equiv_symm := by
        intro _row _row' classified
        cases classified.right
        exact ⟨classified.left, hsame_refl _⟩
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact ⟨leftClassified.left,
          hsame_trans leftClassified.right rightClassified.right⟩
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified.right
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact
        ⟨intervalUnary, endpointUnary, precisionUnary, containmentProvenanceBridge⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, observationReadbackContainment⟩
  }

end BEDC.Derived.ValidatedNumericsUp
