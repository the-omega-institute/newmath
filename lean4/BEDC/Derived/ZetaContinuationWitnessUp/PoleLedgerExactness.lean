import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem ZetaContinuationWitnessPacket_pole_ledger_exactness [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      poleRead authRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
        transports routes provenance name bundle pkg →
      Cont pole zeroLedger poleRead →
        Cont transports routes authRead →
          PkgSig bundle poleRead pkg →
            PkgSig bundle authRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger
                      gamma transports routes provenance name bundle pkg ∧ hsame row poleRead)
                  (fun row : BHist => hsame row poleRead ∧ Cont pole zeroLedger poleRead)
                  (fun row : BHist =>
                    PkgSig bundle poleRead pkg ∧ PkgSig bundle authRead pkg ∧
                      hsame row poleRead)
                  hsame ∧
                hsame poleRead gamma ∧ Cont transports routes provenance ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle poleRead pkg ∧ PkgSig bundle authRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert PkgSig
  intro packet poleRoute _authRoute polePkg authPkg
  have packetKeep := packet
  obtain ⟨_basicAnalytic, _analyticTransport, poleGamma, transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have poleSame : hsame poleRead gamma :=
    cont_deterministic poleRoute poleGamma
  have sourceAtPole :
      (fun row : BHist =>
        ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
          transports routes provenance name bundle pkg ∧ hsame row poleRead) poleRead := by
    exact ⟨packetKeep, hsame_refl poleRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧ hsame row poleRead)
          (fun row : BHist => hsame row poleRead ∧ Cont pole zeroLedger poleRead)
          (fun row : BHist =>
            PkgSig bundle poleRead pkg ∧ PkgSig bundle authRead pkg ∧ hsame row poleRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro poleRead sourceAtPole
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
      exact ⟨source.right, poleRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨polePkg, authPkg, source.right⟩
  }
  exact
    ⟨cert, poleSame, transportProvenance, namePkg, provenancePkg, polePkg, authPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
