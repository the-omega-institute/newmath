import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_root_readiness_source_seal [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory routes →
        UnaryHistory name →
          Cont routes name sourceRead →
            SemanticNameCert
              (fun row : BHist =>
                hsame row sourceRead ∧
                  ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger
                    gamma transports routes provenance name bundle pkg)
              (fun row : BHist => hsame row sourceRead ∧ UnaryHistory sourceRead)
              (fun row : BHist =>
                hsame row sourceRead ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameSource
  have packetSource :
      ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg := packet
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed routesUnary nameUnary routesNameSource
  constructor
  · constructor
    · exact Exists.intro sourceRead ⟨hsame_refl sourceRead, packetSource⟩
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row row' same source
      exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
  · intro _row source
    exact ⟨source.left, sourceUnary⟩
  · intro _row source
    exact ⟨source.left, namePkg, provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
