import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_obligation_triad [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name obligationRead →
            PkgSig bundle obligationRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger
                        gamma transports routes provenance name bundle pkg ∧
                      hsame row obligationRead)
                  (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle obligationRead pkg ∧ hsame row obligationRead)
                  hsame ∧
                Cont basic eta analytic ∧ Cont analytic functional transports ∧
                  Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                    UnaryHistory obligationRead ∧ hsame obligationRead (append routes name) ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle obligationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet routesUnary nameUnary routesNameObligation obligationPkg
  have packetWitness := packet
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed routesUnary nameUnary routesNameObligation
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧
            hsame row obligationRead)
        (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
        (fun row : BHist =>
          PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle obligationRead pkg ∧ hsame row obligationRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro obligationRead
        ⟨packetWitness, hsame_refl obligationRead⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨source.right, unary_transport obligationUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact ⟨namePkg, provenancePkg, obligationPkg, source.right⟩
  }
  exact
    ⟨cert, basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
      transportsRoutesProvenance, obligationUnary, routesNameObligation, namePkg,
      provenancePkg, obligationPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
