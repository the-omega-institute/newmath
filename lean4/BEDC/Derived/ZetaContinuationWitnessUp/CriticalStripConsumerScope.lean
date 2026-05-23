import BEDC.Derived.ZetaContinuationWitnessUp.CriticalStripConsumerNonescape
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_critical_strip_consumer_scope
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      criticalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name criticalRead ->
            PkgSig bundle criticalRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger
                      gamma transports routes provenance name bundle pkg ∧ hsame row criticalRead)
                  (fun row : BHist => hsame row criticalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle criticalRead pkg ∧
                        hsame row criticalRead ∧
                          (Cont criticalRead (BHist.e0 hostTail) routes -> False) ∧
                            (Cont criticalRead (BHist.e1 hostTail) routes -> False))
                  hsame ∧ UnaryHistory criticalRead ∧
                hsame criticalRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame append
  intro packet routesUnary nameUnary routesNameCritical criticalPkg
  have projected :=
    ZetaContinuationWitnessPacket_critical_strip_consumer_nonescape
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (criticalRead := criticalRead) (hostTail := hostTail) (bundle := bundle)
      (pkg := pkg) packet routesUnary nameUnary routesNameCritical criticalPkg
  obtain ⟨criticalUnary, criticalSame, transportsRoutesProvenance, namePkg, provenancePkg,
    criticalPkg', e0Refusal, e1Refusal⟩ := projected
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧ hsame row criticalRead)
          (fun row : BHist => hsame row criticalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle criticalRead pkg ∧
                hsame row criticalRead ∧
                  (Cont criticalRead (BHist.e0 hostTail) routes -> False) ∧
                    (Cont criticalRead (BHist.e1 hostTail) routes -> False))
          hsame := by
    constructor
    · constructor
      · exact Exists.intro criticalRead ⟨packet, hsame_refl criticalRead⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' sameRows
        exact hsame_symm sameRows
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport criticalUnary (hsame_symm source.right)⟩
    · intro _row source
      exact
        ⟨transportsRoutesProvenance, namePkg, provenancePkg, criticalPkg', source.right,
          e0Refusal, e1Refusal⟩
  exact ⟨cert, criticalUnary, criticalSame⟩

end BEDC.Derived.ZetaContinuationWitnessUp
