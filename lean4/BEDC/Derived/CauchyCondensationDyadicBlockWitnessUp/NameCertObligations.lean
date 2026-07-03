import BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCondensationDyadicBlockWitnessNameCertObligations [AskSetup] [PackageSetup]
    {source dyadic witness monotone readback sealRead transport replay provenance name endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory dyadic →
      UnaryHistory witness →
      UnaryHistory monotone →
      UnaryHistory readback →
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
                hsame row monotone ∨ hsame row readback ∨ hsame row sealRead ∨
                  hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                    hsame row name ∨ hsame row endpoint)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont source dyadic witness ∧
                Cont witness monotone readback ∧ Cont readback sealRead endpoint ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
            hsame ∧
          UnaryHistory witness ∧ UnaryHistory readback ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert PkgSig ProbeBundle
  intro sourceUnary dyadicUnary _witnessUnary monotoneUnary _readbackUnary sealUnary
  intro sourceRoute monotoneRoute endpointRoute provenanceSig nameSig
  have witnessClosed : UnaryHistory witness :=
    unary_cont_closed sourceUnary dyadicUnary sourceRoute
  have readbackClosed : UnaryHistory readback :=
    unary_cont_closed witnessClosed monotoneUnary monotoneRoute
  have endpointClosed : UnaryHistory endpoint :=
    unary_cont_closed readbackClosed sealUnary endpointRoute
  constructor
  · constructor
    · constructor
      · exact Exists.intro endpoint (And.intro (hsame_refl endpoint) endpointClosed)
      · intro row source
        exact hsame_refl row
      · intro _row _other sameRows
        exact hsame_symm sameRows
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row other sameRows source
        cases source with
        | intro sourceSame sourceUnaryRow =>
            constructor
            · exact hsame_trans (hsame_symm sameRows) sourceSame
            · exact unary_transport sourceUnaryRow sameRows
    · intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))))
    · intro _row source
      exact
        And.intro source.right
          (And.intro sourceRoute
            (And.intro monotoneRoute
              (And.intro endpointRoute (And.intro provenanceSig nameSig))))
  · exact And.intro witnessClosed (And.intro readbackClosed endpointClosed)

end BEDC.Derived.CauchyCondensationDyadicBlockWitnessUp
