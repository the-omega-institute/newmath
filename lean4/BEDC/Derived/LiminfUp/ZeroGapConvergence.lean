import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfLimsupZeroGapConvergence [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic terminal transport replay provenance localName upperEnvelope
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      UnaryHistory upperEnvelope →
        Cont lowerCut upperEnvelope dyadic →
          Cont terminal transport sealRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row lowerCut ∨ hsame row upperEnvelope ∨ hsame row terminal) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperEnvelope ∨
                        hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont lowerCut upperEnvelope dyadic ∧
                        Cont terminal transport sealRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sealRead ∧ Cont sequence lowerCut dyadic := by
  -- BEDC touchpoint anchor: LiminfCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier upperEnvelopeUnary lowerUpperRoute terminalTransport provenancePkg sealPkg
  have lowerEnvelope :=
    LiminfTailLowerEnvelopeCompatibility
      (sequence := sequence)
      (lowerCut := lowerCut)
      (dyadic := dyadic)
      (upperEnvelope := upperEnvelope)
      (terminal := terminal)
      (transport := transport)
      (replay := replay)
      (provenance := provenance)
      (localName := localName)
      (sealRead := sealRead)
      (bundle := bundle)
      (pkg := pkg)
      carrier upperEnvelopeUnary lowerUpperRoute terminalTransport provenancePkg sealPkg
  have sequenceRoute : Cont sequence lowerCut dyadic :=
    carrier.right.right.right.right.right.right.right.right.left
  exact ⟨lowerEnvelope.left, lowerEnvelope.right, sequenceRoute⟩

end BEDC.Derived.LiminfUp
