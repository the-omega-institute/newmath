import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_namecert_package [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      packageRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name packageRead →
            PkgSig bundle packageRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger
                      gamma transports routes provenance name bundle pkg ∧
                        hsame row packageRead)
                  (fun row : BHist => UnaryHistory row ∧ hsame row packageRead)
                  (fun row : BHist =>
                    PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle packageRead pkg ∧ hsame row packageRead)
                  hsame ∧
                UnaryHistory packageRead ∧ hsame packageRead (append routes name) ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle packageRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet routesUnary nameUnary routesNamePackage packageReadPkg
  have packetKeep := packet
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have packageReadUnary : UnaryHistory packageRead :=
    unary_cont_closed routesUnary nameUnary routesNamePackage
  have sourcePackage :
      (fun row : BHist =>
        ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
          transports routes provenance name bundle pkg ∧ hsame row packageRead)
          packageRead := by
    exact ⟨packetKeep, hsame_refl packageRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧ hsame row packageRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row packageRead)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle packageRead pkg ∧ hsame row packageRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro packageRead sourcePackage
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨unary_transport packageReadUnary (hsame_symm source.right), source.right⟩
      ledger_sound := by
        intro _row source
        exact ⟨namePkg, provenancePkg, packageReadPkg, source.right⟩
    }
  exact
    ⟨cert, packageReadUnary, routesNamePackage, namePkg, provenancePkg, packageReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
