import BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp.NameCertObligations

namespace BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCondensationDyadicBlockWitnessRealHandoff [AskSetup] [PackageSetup]
    {source dyadic witness monotone readback sealRead transport replay provenance name endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory dyadic →
        UnaryHistory monotone →
          UnaryHistory sealRead →
            Cont source dyadic witness →
              Cont witness monotone readback →
                Cont readback sealRead endpoint →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle name pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row dyadic ∨ hsame row witness ∨
                              hsame row monotone ∨ hsame row readback ∨
                                hsame row sealRead ∨ hsame row transport ∨
                                  hsame row replay ∨ hsame row provenance ∨
                                    hsame row name ∨ hsame row endpoint)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont source dyadic witness ∧
                              Cont witness monotone readback ∧
                                Cont readback sealRead endpoint ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle name pkg)
                          hsame ∧
                        UnaryHistory witness ∧ UnaryHistory readback ∧
                          UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert PkgSig ProbeBundle
  intro sourceUnary dyadicUnary monotoneUnary sealUnary
  intro sourceRoute monotoneRoute endpointRoute provenanceSig nameSig
  have witnessClosed : UnaryHistory witness :=
    unary_cont_closed sourceUnary dyadicUnary sourceRoute
  have readbackClosed : UnaryHistory readback :=
    unary_cont_closed witnessClosed monotoneUnary monotoneRoute
  exact
    CauchyCondensationDyadicBlockWitnessNameCertObligations
      (source := source) (dyadic := dyadic) (witness := witness)
      (monotone := monotone) (readback := readback) (sealRead := sealRead)
      (transport := transport) (replay := replay) (provenance := provenance)
      (name := name) (endpoint := endpoint) (bundle := bundle) (pkg := pkg)
      sourceUnary dyadicUnary witnessClosed monotoneUnary readbackClosed sealUnary
      sourceRoute monotoneRoute endpointRoute provenanceSig nameSig

end BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp
