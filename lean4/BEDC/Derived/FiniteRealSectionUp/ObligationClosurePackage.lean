import BEDC.Derived.FiniteRealSectionUp.DyadicSealFactorization
import BEDC.Derived.FiniteRealSectionUp.RefinementNoncollapse

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FiniteRealSection_obligation_closure_package [AskSetup] [PackageSetup]
    {q W R D E H C P N qW qWR qWRD qWRDE terminal refined ambient : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory q → UnaryHistory W → UnaryHistory R → UnaryHistory D →
      UnaryHistory E → UnaryHistory N → UnaryHistory C → Cont q W qW →
        Cont qW R qWR → Cont qWR D qWRD → Cont qWRD E qWRDE →
          Cont qWRDE N terminal → Cont terminal C refined →
            PkgSig bundle terminal pkg → PkgSig bundle refined pkg →
              hsame ambient (BHist.e0 refined) →
                FieldFaithful.fields (FiniteRealSectionUp.mk q W R D E H C P N) =
                    [q, W, R, D, E, H, C, P, N] ∧
                  hsame qWRDE (append (append (append (append q W) R) D) E) ∧
                    UnaryHistory refined ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row refined ∧ UnaryHistory row)
                        (fun row : BHist => hsame row terminal ∨ hsame row refined)
                        (fun row : BHist => hsame row refined ∧ PkgSig bundle refined pkg)
                        hsame ∧
                      (hsame ambient refined → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame Cont
  intro unaryQ unaryW unaryR unaryD unaryE unaryN unaryC requestWindow windowReadback
    readbackTolerance toleranceSeal sealTerminal terminalRefined terminalPkg refinedPkg
    ambientExtended
  have sealPackage :=
    FiniteRealSection_dyadic_seal_factorization
      unaryQ unaryW unaryR unaryD unaryE unaryN requestWindow windowReadback
      readbackTolerance toleranceSeal sealTerminal terminalPkg
  have refinedPackage :=
    FiniteRealSection_refinement_noncollapse (H := H) (P := P)
      unaryQ unaryW unaryR unaryD unaryE unaryN unaryC requestWindow windowReadback
      readbackTolerance toleranceSeal sealTerminal terminalRefined refinedPkg ambientExtended
  exact
    ⟨refinedPackage.right.left, sealPackage.left, refinedPackage.left,
      refinedPackage.right.right.left, refinedPackage.right.right.right⟩

end BEDC.Derived.FiniteRealSectionUp
