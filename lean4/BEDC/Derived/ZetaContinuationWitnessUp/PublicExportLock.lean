import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_public_export_lock [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name exportRow →
            PkgSig bundle exportRow pkg →
              SemanticNameCert
                    (fun row : BHist =>
                      ZetaContinuationWitnessPacket basic eta analytic pole functional
                          zeroLedger gamma transports routes provenance name bundle pkg ∧
                        hsame row exportRow)
                    (fun row : BHist =>
                      UnaryHistory row ∧ hsame row (append routes name))
                    (fun _row : BHist =>
                      PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle exportRow pkg)
                    hsame ∧
                Cont basic eta analytic ∧ Cont analytic functional transports ∧
                  Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                    UnaryHistory exportRow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameExport exportPkg
  have packetWitness := packet
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routesUnary nameUnary routesNameExport
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
                transports routes provenance name bundle pkg ∧
              hsame row exportRow)
          (fun row : BHist => UnaryHistory row ∧ hsame row (append routes name))
          (fun _row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle exportRow pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exportRow ⟨packetWitness, hsame_refl exportRow⟩
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
          intro _row _row' sameRows source
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨unary_transport exportUnary (hsame_symm source.right),
            hsame_trans source.right routesNameExport⟩
      ledger_sound := by
        intro _row _source
        exact ⟨namePkg, provenancePkg, exportPkg⟩
    }
  exact
    ⟨cert, basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
      transportsRoutesProvenance, exportUnary⟩

end BEDC.Derived.ZetaContinuationWitnessUp
