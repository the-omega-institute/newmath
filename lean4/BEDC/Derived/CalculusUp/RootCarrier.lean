import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CalculusRootCarrier [AskSetup] [PackageSetup]
    (continuous derivative integral limit real readback dyadic transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory continuous ∧ UnaryHistory derivative ∧ UnaryHistory integral ∧
    UnaryHistory limit ∧ UnaryHistory real ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont continuous derivative integral ∧
          Cont readback dyadic real ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem CalculusRootCarrier_admission [AskSetup] [PackageSetup]
    {continuous derivative integral limit real readback dyadic transport replay provenance
      localName derivativeRead integralRead limitRead dyadicRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootCarrier continuous derivative integral limit real readback dyadic transport replay
        provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont continuous integral integralRead →
          Cont continuous limit limitRead →
            Cont readback dyadic dyadicRead →
              Cont dyadic real realRead →
                Cont real localName namedRead →
                  PkgSig bundle namedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row continuous ∨ hsame row derivative ∨
                            hsame row integral ∨ hsame row limit ∨ hsame row real ∨
                              hsame row readback ∨ hsame row dyadic ∨
                                hsame row transport ∨ hsame row replay ∨
                                  hsame row provenance ∨ hsame row localName ∨
                                    hsame row derivativeRead ∨ hsame row integralRead ∨
                                      hsame row limitRead ∨ hsame row dyadicRead ∨
                                        hsame row realRead ∨ hsame row namedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont continuous derivative integral ∧
                            Cont readback dyadic real ∧
                              Cont continuous derivative derivativeRead ∧
                                Cont continuous integral integralRead ∧
                                  Cont continuous limit limitRead ∧
                                    Cont readback dyadic dyadicRead ∧
                                      Cont dyadic real realRead ∧
                                        Cont real localName namedRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle localName pkg ∧
                                              PkgSig bundle namedRead pkg)
                        hsame ∧
                      UnaryHistory derivativeRead ∧ UnaryHistory integralRead ∧
                        UnaryHistory limitRead ∧ UnaryHistory dyadicRead ∧
                          UnaryHistory realRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier derivativeRoute integralRoute limitRoute dyadicRoute realRoute namedRoute namedPkg
  obtain ⟨continuousUnary, derivativeUnary, integralUnary, limitUnary, realUnary,
    readbackUnary, dyadicUnary, _transportUnary, _replayUnary, provenanceUnary,
    localNameUnary, continuousDerivativeIntegral, readbackDyadicReal, provenancePkg,
    localNamePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed continuousUnary integralUnary integralRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed continuousUnary limitUnary limitRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary dyadicUnary dyadicRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary realUnary realRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary localNameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row continuous ∨ hsame row derivative ∨ hsame row integral ∨
              hsame row limit ∨ hsame row real ∨ hsame row readback ∨ hsame row dyadic ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row derivativeRead ∨ hsame row integralRead ∨
                    hsame row limitRead ∨ hsame row dyadicRead ∨ hsame row realRead ∨
                      hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuous derivative integral ∧
              Cont readback dyadic real ∧ Cont continuous derivative derivativeRead ∧
                Cont continuous integral integralRead ∧ Cont continuous limit limitRead ∧
                  Cont readback dyadic dyadicRead ∧ Cont dyadic real realRead ∧
                    Cont real localName namedRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr source.left)))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, continuousDerivativeIntegral, readbackDyadicReal, derivativeRoute,
          integralRoute, limitRoute, dyadicRoute, realRoute, namedRoute, provenancePkg,
          localNamePkg, namedPkg⟩
  }
  exact
    ⟨cert, derivativeReadUnary, integralReadUnary, limitReadUnary, dyadicReadUnary,
      realReadUnary, namedReadUnary⟩

end BEDC.Derived.CalculusUp
