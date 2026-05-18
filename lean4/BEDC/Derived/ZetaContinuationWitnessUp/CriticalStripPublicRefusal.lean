import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_critical_strip_public_refusal [AskSetup]
    [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      criticalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name criticalRead ->
            PkgSig bundle criticalRead pkg ->
              SemanticNameCert
                    (fun row : BHist =>
                      ZetaContinuationWitnessPacket basic eta analytic pole functional
                        zeroLedger gamma transports routes provenance name bundle pkg ∧
                          hsame row criticalRead)
                    (fun row : BHist => hsame row criticalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle criticalRead pkg ∧
                          hsame row criticalRead)
                    hsame ∧
                  UnaryHistory criticalRead ∧ hsame criticalRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro packet routesUnary nameUnary routesNameCritical criticalPkg
  have projected :=
    ZetaContinuationWitnessPacket_critical_strip_input_refusal
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (criticalRead := criticalRead) (bundle := bundle) (pkg := pkg)
      packet routesUnary nameUnary routesNameCritical
  obtain ⟨criticalUnary, criticalSame, transportsRoutesProvenance, namePkg,
    provenancePkg⟩ := projected
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧ hsame row criticalRead)
          (fun row : BHist => hsame row criticalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle criticalRead pkg ∧
                hsame row criticalRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro criticalRead ⟨packet, hsame_refl criticalRead⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _row' same
        exact hsame_symm same
      · intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport criticalUnary (hsame_symm source.right)⟩
    · intro _row source
      exact ⟨transportsRoutesProvenance, namePkg, provenancePkg, criticalPkg, source.right⟩
  exact ⟨cert, criticalUnary, criticalSame⟩

end BEDC.Derived.ZetaContinuationWitnessUp
