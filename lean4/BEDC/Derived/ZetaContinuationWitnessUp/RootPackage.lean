import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_zero_ledger_nonescape [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name zeroRead ->
            PkgSig bundle zeroRead pkg ->
              UnaryHistory zeroRead ∧ hsame zeroRead (append routes name) ∧
                Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle zeroRead pkg ∧
                      (Cont zeroRead (BHist.e0 hostTail) routes -> False) ∧
                        (Cont zeroRead (BHist.e1 hostTail) routes -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameZero zeroReadPkg
  obtain ⟨_basicAnalytic, _analyticTransport, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed routesUnary nameUnary routesNameZero
  have e0Refusal : Cont zeroRead (BHist.e0 hostTail) routes -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.left routesNameZero back
  have e1Refusal : Cont zeroRead (BHist.e1 hostTail) routes -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.right routesNameZero back
  exact
    ⟨zeroReadUnary, routesNameZero, poleZeroLedgerGamma, transportsRoutesProvenance, namePkg,
      provenancePkg, zeroReadPkg, e0Refusal, e1Refusal⟩

theorem ZetaContinuationWitnessPacket_root_package [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name rootRead ->
            PkgSig bundle rootRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
                    transports routes provenance name bundle pkg ∧ hsame row rootRead)
                (fun row : BHist => hsame row rootRead ∧ UnaryHistory rootRead)
                (fun row : BHist =>
                  PkgSig bundle rootRead pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle provenance pkg ∧ hsame row rootRead)
                hsame ∧
              UnaryHistory rootRead ∧ hsame rootRead (append routes name) ∧
                PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet routesUnary nameUnary routesNameRoot rootReadPkg
  have sourcePacket := packet
  obtain ⟨_basicAnalytic, _analyticTransport, _poleGamma, _transportProvenance, namePkg,
    provenancePkg⟩ := packet
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routesUnary nameUnary routesNameRoot
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
            transports routes provenance name bundle pkg ∧ hsame row rootRead)
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory rootRead)
        (fun row : BHist =>
          PkgSig bundle rootRead pkg ∧ PkgSig bundle name pkg ∧
            PkgSig bundle provenance pkg ∧ hsame row rootRead)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro rootRead ⟨sourcePacket, hsame_refl rootRead⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, rootUnary⟩
    · intro _row source
      exact ⟨rootReadPkg, namePkg, provenancePkg, source.right⟩
  exact ⟨cert, rootUnary, routesNameRoot, namePkg, provenancePkg, rootReadPkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
