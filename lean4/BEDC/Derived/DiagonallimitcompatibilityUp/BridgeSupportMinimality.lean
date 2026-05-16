import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityBridgeSupportMinimality [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      routeLedger routeEndpoint consumer sealGate terminal support : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal triangle routeLedger →
        Cont routeLedger dyadic routeEndpoint →
          Cont routeEndpoint windows consumer →
            Cont consumer readback sealGate →
              Cont sealGate realSeal terminal →
                Cont route cert support →
                  PkgSig bundle support pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic
                            windows readback realSeal transport route provenance cert bundle
                            pkg ∧ hsame row support)
                      (fun row : BHist =>
                        Cont diagonal triangle routeLedger ∧
                          Cont routeLedger dyadic routeEndpoint ∧
                            Cont routeEndpoint windows consumer ∧
                              Cont consumer readback sealGate ∧
                                Cont sealGate realSeal terminal ∧
                                  Cont route cert row ∧ PkgSig bundle support pkg)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle support pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier diagonalTriangleLedger ledgerDyadicEndpoint endpointWindowsConsumer
    consumerReadbackSealGate sealGateRealTerminal routeCertSupport supportPkg
  have carrierFull :
      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg :=
    carrier
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, _realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have supportUnary : UnaryHistory support :=
    unary_cont_closed routeUnary certUnary routeCertSupport
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro support (And.intro carrierFull (hsame_refl support))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact source.left
        · exact hsame_trans (hsame_symm sameRows) source.right
    }
    pattern_sound := by
      intro row source
      constructor
      · exact diagonalTriangleLedger
      · constructor
        · exact ledgerDyadicEndpoint
        · constructor
          · exact endpointWindowsConsumer
          · constructor
            · exact consumerReadbackSealGate
            · constructor
              · exact sealGateRealTerminal
              · constructor
                · cases source.right
                  exact routeCertSupport
                · exact supportPkg
    ledger_sound := by
      intro row source
      cases source.right
      exact And.intro supportUnary supportPkg
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
