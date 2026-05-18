import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
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
                UnaryHistory obligationRead ∧ hsame obligationRead (append routes name) ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle obligationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet routesUnary nameUnary routesNameObligation obligationPkg
  have sourcePacket := packet
  obtain ⟨_basicAnalytic, _analyticTransport, _poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed routesUnary nameUnary routesNameObligation
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧ hsame row obligationRead)
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle obligationRead pkg ∧ hsame row obligationRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro obligationRead ⟨sourcePacket, hsame_refl obligationRead⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport obligationUnary (hsame_symm source.right)⟩
    · intro _row source
      exact ⟨namePkg, provenancePkg, obligationPkg, source.right⟩
  exact
    ⟨cert, obligationUnary, routesNameObligation, namePkg, provenancePkg, obligationPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
