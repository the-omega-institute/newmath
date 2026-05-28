import BEDC.Derived.SeparatedMetricUp.CauchyUniquenessRootPackage
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricPacket_namecert_ledger_exhaustion [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint limitRead zeroRead classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg →
      Cont limitWitness completionRoute limitRead →
        Cont limitRead zeroDistance zeroRead →
          Cont zeroRead apartness classifierRead →
            PkgSig bundle classifierRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute
                    transport provenance nameCert endpoint bundle pkg ∧
                    (hsame row nameCert ∨ hsame row classifierRead))
                (fun _row : BHist =>
                  Cont limitWitness completionRoute limitRead ∧
                    Cont limitRead zeroDistance zeroRead ∧
                      Cont zeroRead apartness classifierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle nameCert pkg ∧
                    PkgSig bundle classifierRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet limitRoute zeroRoute classifierRoute classifierPkg
  have packetWhole := packet
  have rootPackage :=
    SeparatedMetricPacket_cauchy_uniqueness_root_package
      (metric := metric) (apartness := apartness) (zeroDistance := zeroDistance)
      (limitWitness := limitWitness) (completionRoute := completionRoute)
      (transport := transport) (provenance := provenance) (nameCert := nameCert)
      (endpoint := endpoint) (limitRead := limitRead) (zeroRead := zeroRead)
      (classifierRead := classifierRead) (bundle := bundle) (pkg := pkg)
      packet limitRoute zeroRoute classifierRoute classifierPkg
  obtain ⟨_metricUnary, _apartnessUnary, _zeroUnary, _limitWitnessUnary,
    _completionUnary, _limitReadUnary, _zeroReadUnary, classifierUnary, _limitRouteOut,
    _zeroRouteOut, _classifierRouteOut, nameCertPkg, classifierPkgOut⟩ := rootPackage
  obtain ⟨_metricPacketUnary, _apartnessPacketUnary, _zeroPacketUnary,
    _limitWitnessPacketUnary, _completionPacketUnary, _transportUnary,
    _provenanceUnary, nameCertUnary, _endpointUnary, _apartnessZeroLimit,
    _limitCompletionTransport, _transportProvenanceEndpoint, _nameCertPkgPacket⟩ :=
    packet
  have sourceNameCert :
      (fun row : BHist =>
        SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute
          transport provenance nameCert endpoint bundle pkg ∧
          (hsame row nameCert ∨ hsame row classifierRead)) nameCert := by
    exact ⟨packetWhole, Or.inl (hsame_refl nameCert)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro nameCert sourceNameCert
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
        cases source with
        | intro sourcePacket sourceRows =>
            constructor
            · exact sourcePacket
            · cases sourceRows with
              | inl sameNameCert =>
                  exact Or.inl (hsame_trans (hsame_symm sameRows) sameNameCert)
              | inr sameClassifier =>
                  exact Or.inr (hsame_trans (hsame_symm sameRows) sameClassifier)
    }
    pattern_sound := by
      intro _row _source
      exact ⟨limitRoute, zeroRoute, classifierRoute⟩
    ledger_sound := by
      intro _row source
      cases source with
      | intro _sourcePacket sourceRows =>
          cases sourceRows with
          | inl sameNameCert =>
              exact
                ⟨unary_transport nameCertUnary (hsame_symm sameNameCert), nameCertPkg,
                  classifierPkgOut⟩
          | inr sameClassifier =>
              exact
                ⟨unary_transport classifierUnary (hsame_symm sameClassifier), nameCertPkg,
                  classifierPkgOut⟩
  }

end BEDC.Derived.SeparatedMetricUp
