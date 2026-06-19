import BEDC.Derived.CalculusUp

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusLocatedCompactDependencyRoute [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance localName
      derivativeRead graphRead regSeqRead realSeal locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont derivativeRead readback graphRead →
          Cont graphRead transport regSeqRead →
            Cont regSeqRead real realSeal →
              Cont realSeal localName locatedRead →
                PkgSig bundle locatedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row derivativeRead ∨ hsame row graphRead ∨
                          hsame row regSeqRead ∨ hsame row realSeal ∨ hsame row locatedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont continuous derivative derivativeRead ∧
                          Cont derivativeRead readback graphRead ∧
                            Cont graphRead transport regSeqRead ∧
                              Cont regSeqRead real realSeal ∧
                                Cont realSeal localName locatedRead ∧
                                  PkgSig bundle locatedRead pkg)
                      hsame ∧
                    UnaryHistory locatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier derivativeRoute graphRoute regSeqRoute realSealRoute locatedRoute locatedPkg
  obtain ⟨realUnary, _limitUnary, continuousUnary, derivativeUnary, _integralUnary,
    readbackUnary, transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _realLimitRoute, _continuousDerivativeIntegral, _derivativeReadbackTransport,
    _transportReplayLocalName, _provenancePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed derivativeReadUnary readbackUnary graphRoute
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed graphReadUnary transportUnary regSeqRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regSeqReadUnary realUnary realSealRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed realSealUnary localNameUnary locatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row graphRead ∨ hsame row regSeqRead ∨
              hsame row realSeal ∨ hsame row locatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuous derivative derivativeRead ∧
              Cont derivativeRead readback graphRead ∧ Cont graphRead transport regSeqRead ∧
                Cont regSeqRead real realSeal ∧ Cont realSeal localName locatedRead ∧
                  PkgSig bundle locatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRead ⟨hsame_refl locatedRead, locatedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeRoute, graphRoute, regSeqRoute, realSealRoute,
          locatedRoute, locatedPkg⟩
  }
  exact ⟨cert, locatedReadUnary⟩

end BEDC.Derived.CalculusUp
