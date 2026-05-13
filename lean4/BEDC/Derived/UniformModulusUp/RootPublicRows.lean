import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_root_carrier_public_row [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead coverageRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont bundleRow radius compactRead ->
        Cont compactRead coverage coverageRead ->
          Cont coverageRead nameRow exported ->
            PkgSig bundle exported pkg ->
              UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory bundleRow ∧
                UnaryHistory radius ∧ UnaryHistory coverage ∧ UnaryHistory compactRead ∧
                  UnaryHistory coverageRead ∧ UnaryHistory exported ∧
                    Cont tolerance bundleRow coverage ∧ Cont bundleRow radius compactRead ∧
                      Cont compactRead coverage coverageRead ∧
                        Cont coverageRead nameRow exported ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet compactRoute coverageReadRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    coverageRoute, _transportRoute, _foldRoute, _provenanceRoute, _packetPkg⟩ := packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary coverageRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have coverageReadUnary : UnaryHistory coverageRead :=
    unary_cont_closed compactReadUnary coverageUnary coverageReadRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed coverageReadUnary nameRowUnary exportRoute
  exact
    ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, coverageUnary,
      compactReadUnary, coverageReadUnary, exportedUnary, coverageRoute, compactRoute,
      coverageReadRoute, exportRoute, exportPkg⟩

theorem UniformModulusPacket_root_classifier_transport_row [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow tolerance' precision' bundleRow' radius' coverage' pointwise' foldLedger'
      transport' provenance' nameRow' compactRead' pointwiseRead' exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      hsame tolerance tolerance' ->
        hsame precision precision' ->
          hsame bundleRow bundleRow' ->
            hsame radius radius' ->
              hsame nameRow nameRow' ->
                UnaryHistory pointwise' ->
                  Cont tolerance' bundleRow' coverage' ->
                    Cont coverage' pointwise' transport' ->
                      Cont precision' radius' foldLedger' ->
                        Cont foldLedger' nameRow' provenance' ->
                          Cont bundleRow' radius' compactRead' ->
                            Cont compactRead' pointwise' pointwiseRead' ->
                              Cont pointwiseRead' foldLedger' exported ->
                                PkgSig bundle provenance' pkg ->
                                  PkgSig bundle exported pkg ->
                                    UniformModulusPacket tolerance' precision' bundleRow'
                                      radius' coverage' pointwise' foldLedger' transport'
                                      provenance' nameRow' bundle pkg ∧
                                      hsame provenance provenance' ∧
                                        UnaryHistory compactRead' ∧
                                          UnaryHistory pointwiseRead' ∧
                                            UnaryHistory exported ∧
                                              Cont compactRead' pointwise' pointwiseRead' ∧
                                                Cont pointwiseRead' foldLedger' exported ∧
                                                  PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg hsame
  intro packet sameTolerance samePrecision sameBundleRow sameRadius sameNameRow pointwiseUnary'
    coverageRoute' transportRoute' foldRoute' provenanceRoute' compactRoute' pointwiseRoute'
    exportRoute' provenancePkg' exportPkg
  have transported :=
    UniformModulusPacket_classifier_transport_stability packet sameTolerance samePrecision
      sameBundleRow sameRadius sameNameRow coverageRoute' transportRoute' foldRoute'
      provenanceRoute' provenancePkg'
  have sameProvenance : hsame provenance provenance' :=
    transported.right
  obtain ⟨_toleranceUnaryPrime, precisionUnaryPrime, bundleRowUnaryPrime, radiusUnaryPrime,
    _nameRowUnaryPrime, _coverageRoutePrime, _transportRoutePrime, _foldRoutePrime,
    _provenanceRoutePrime, _packetPkgPrime⟩ := transported.left
  have compactReadUnary' : UnaryHistory compactRead' :=
    unary_cont_closed bundleRowUnaryPrime radiusUnaryPrime compactRoute'
  have foldLedgerUnary' : UnaryHistory foldLedger' :=
    unary_cont_closed precisionUnaryPrime radiusUnaryPrime foldRoute'
  have pointwiseReadUnary' : UnaryHistory pointwiseRead' :=
    unary_cont_closed compactReadUnary' pointwiseUnary' pointwiseRoute'
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed pointwiseReadUnary' foldLedgerUnary' exportRoute'
  exact
    ⟨transported.left, sameProvenance, compactReadUnary', pointwiseReadUnary', exportedUnary,
      pointwiseRoute', exportRoute', exportPkg⟩

end BEDC.Derived.UniformModulusUp
