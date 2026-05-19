import BEDC.Derived.ZnormalUp.RootTotalHostRefusal
import BEDC.Derived.ZnormalUp.RootUnblockNonescapeLedger

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalDivergenceOracleNonescapeRow [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      downstream oracleBlock : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead transports downstream →
          Cont downstream routes oracleBlock →
            PkgSig bundle downstream pkg →
              PkgSig bundle oracleBlock pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row oracleBlock ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                        hsame row normal ∨ hsame row continuation ∨
                          hsame row normalRead ∨ hsame row downstream ∨
                            hsame row oracleBlock)
                    (fun row : BHist =>
                      hsame row oracleBlock ∧ PkgSig bundle oracleBlock pkg)
                    hsame ∧
                  UnaryHistory normalRead ∧ UnaryHistory downstream ∧
                    UnaryHistory oracleBlock ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet normalContinuationRead normalReadTransportsDownstream downstreamRoutesOracle
    downstreamPkg oraclePkg
  obtain ⟨cert, normalReadUnary, downstreamUnary, oracleUnary⟩ :=
    ZnormalRootUnblockNonescapeLedger packet normalContinuationRead
      normalReadTransportsDownstream downstreamRoutesOracle oraclePkg
  obtain ⟨_normalReadUnary, _downstreamUnary, namePkg, provenancePkg, downstreamPkg'⟩ :=
    ZnormalRootTotalHostRefusal packet normalContinuationRead normalReadTransportsDownstream
      downstreamPkg
  exact
    ⟨cert, normalReadUnary, downstreamUnary, oracleUnary, namePkg, provenancePkg,
      downstreamPkg'⟩

end BEDC.Derived.ZnormalUp
