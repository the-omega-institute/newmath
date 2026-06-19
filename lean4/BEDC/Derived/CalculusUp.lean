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

def CalculusRootDerivativeIntegralCarrier [AskSetup] [PackageSetup]
    (real limit continuous derivative integral readback transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory real ∧ UnaryHistory limit ∧ UnaryHistory continuous ∧
    UnaryHistory derivative ∧ UnaryHistory integral ∧ UnaryHistory readback ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont real limit continuous ∧
          Cont continuous derivative integral ∧ Cont derivative readback transport ∧
            Cont transport replay localName ∧ PkgSig bundle provenance pkg

theorem CalculusRootDerivativeIntegralCarrier_admission [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance
      localName derivativeRead integralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont integral readback integralRead →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row derivativeRead ∨ hsame row integralRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row real ∨ hsame row limit ∨ hsame row continuous ∨
                  hsame row derivative ∨ hsame row integral ∨ hsame row readback ∨
                    hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row derivativeRead ∨ hsame row integralRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont real limit continuous ∧
                  Cont continuous derivative integral ∧ Cont derivative readback transport ∧
                    Cont transport replay localName ∧ Cont continuous derivative derivativeRead ∧
                      Cont integral readback integralRead ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory derivativeRead ∧ UnaryHistory integralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier derivativeRoute integralRoute
  obtain ⟨realUnary, limitUnary, continuousUnary, derivativeUnary, integralUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    realLimitRoute, continuousDerivativeRoute, derivativeTransportRoute,
    transportReplayRoute, provenancePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have sourceDerivative :
      (hsame derivativeRead derivativeRead ∨ hsame derivativeRead integralRead) ∧
        UnaryHistory derivativeRead :=
    ⟨Or.inl (hsame_refl derivativeRead), derivativeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row derivativeRead ∨ hsame row integralRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row real ∨ hsame row limit ∨ hsame row continuous ∨
              hsame row derivative ∨ hsame row integral ∨ hsame row readback ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row derivativeRead ∨ hsame row integralRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont real limit continuous ∧
              Cont continuous derivative integral ∧ Cont derivative readback transport ∧
                Cont transport replay localName ∧ Cont continuous derivative derivativeRead ∧
                  Cont integral readback integralRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro derivativeRead sourceDerivative
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
        constructor
        · cases source.left with
          | inl sameDerivative =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDerivative)
          | inr sameIntegral =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameIntegral)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDerivative =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameDerivative))))))))))
      | inr sameIntegral =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr sameIntegral))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, realLimitRoute, continuousDerivativeRoute, derivativeTransportRoute,
          transportReplayRoute, derivativeRoute, integralRoute, provenancePkg⟩
  }
  exact ⟨cert, derivativeReadUnary, integralReadUnary⟩

theorem CalculusRiemannIntegralDependencyFactorization [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance localName
      derivativeRead integralRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont integral readback integralRead →
          Cont derivativeRead integralRead endpointRead →
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row derivative ∨ hsame row integral ∨ hsame row derivativeRead ∨
                    hsame row integralRead ∨ hsame row endpointRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont continuous derivative derivativeRead ∧
                    Cont integral readback integralRead ∧
                      Cont derivativeRead integralRead endpointRead ∧
                        PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier derivativeRoute integralRoute endpointRoute
  obtain ⟨_realUnary, _limitUnary, continuousUnary, derivativeUnary, integralUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _realLimitRoute, _continuousDerivativeRoute, _derivativeTransportRoute,
    _transportReplayRoute, provenancePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary endpointRoute
  have endpointSource :
      (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row) endpointRead := by
    exact ⟨hsame_refl endpointRead, endpointReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivative ∨ hsame row integral ∨ hsame row derivativeRead ∨
              hsame row integralRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuous derivative derivativeRead ∧
              Cont integral readback integralRead ∧
                Cont derivativeRead integralRead endpointRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead endpointSource
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
      exact ⟨source.right, derivativeRoute, integralRoute, endpointRoute, provenancePkg⟩
  }
  exact ⟨cert, endpointReadUnary⟩

theorem CalculusRootLimitDerivativeIntegralTriad [AskSetup] [PackageSetup]
    {C D I L Q Y R H T P N derivativeRead integralRead limitRead toleranceRead realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory Q →
              UnaryHistory Y →
                UnaryHistory R →
                  Cont C D derivativeRead →
                    Cont C I integralRead →
                      Cont C L limitRead →
                        Cont Q Y toleranceRead →
                          Cont toleranceRead R realRead →
                            hsame H (append P N) →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row C ∨ hsame row D ∨ hsame row I ∨
                                          hsame row L ∨ hsame row Q ∨ hsame row Y ∨
                                            hsame row R ∨ hsame row realRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont C D derivativeRead ∧
                                            Cont C I integralRead ∧ Cont C L limitRead ∧
                                              Cont Q Y toleranceRead ∧
                                                Cont toleranceRead R realRead ∧
                                                  hsame H (append P N))
                                      hsame ∧
                                    UnaryHistory derivativeRead ∧ UnaryHistory integralRead ∧
                                      UnaryHistory limitRead ∧ UnaryHistory toleranceRead ∧
                                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert Pkg
  intro hC hD hI hL hQ hY hR derivativeRoute integralRoute limitRoute toleranceRoute
    realRoute structuralSame _pkgP _pkgN
  have hDerivative : UnaryHistory derivativeRead := unary_cont_closed hC hD derivativeRoute
  have hIntegral : UnaryHistory integralRead := unary_cont_closed hC hI integralRoute
  have hLimit : UnaryHistory limitRead := unary_cont_closed hC hL limitRoute
  have hTolerance : UnaryHistory toleranceRead := unary_cont_closed hQ hY toleranceRoute
  have hReal : UnaryHistory realRead := unary_cont_closed hTolerance hR realRoute
  have sourceReal : hsame realRead realRead ∧ UnaryHistory realRead :=
    ⟨hsame_refl realRead, hReal⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨ hsame row Q ∨
              hsame row Y ∨ hsame row R ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeRead ∧ Cont C I integralRead ∧
              Cont C L limitRead ∧ Cont Q Y toleranceRead ∧
                Cont toleranceRead R realRead ∧ hsame H (append P N))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeRoute, integralRoute, limitRoute, toleranceRoute, realRoute,
          structuralSame⟩
  }
  exact ⟨cert, hDerivative, hIntegral, hLimit, hTolerance, hReal⟩

theorem CalculusRootLocalLinearityComposition [AskSetup] [PackageSetup]
    {C D L Q Y R H T P N derivativeLeft derivativeRight comparisonRead dyadicRead
      realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory L →
          UnaryHistory Q →
            UnaryHistory Y →
              UnaryHistory R →
                UnaryHistory H →
                  UnaryHistory T →
                    UnaryHistory N →
                      Cont C D derivativeLeft →
                        Cont derivativeLeft D derivativeRight →
                          Cont D L comparisonRead →
                            Cont Q Y dyadicRead →
                              Cont dyadicRead R realRead →
                                Cont realRead N namedRead →
                                  hsame H (append T P) →
                                    PkgSig bundle P pkg →
                                      PkgSig bundle N pkg →
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row namedRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row C ∨ hsame row D ∨ hsame row L ∨
                                                hsame row Q ∨ hsame row Y ∨ hsame row R ∨
                                                  hsame row namedRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont C D derivativeLeft ∧
                                                  Cont derivativeLeft D derivativeRight ∧
                                                    Cont D L comparisonRead ∧
                                                      Cont Q Y dyadicRead ∧
                                                        Cont dyadicRead R realRead ∧
                                                          Cont realRead N namedRead ∧
                                                            hsame H (append T P))
                                            hsame ∧
                                          UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert Pkg
  intro hC hD hL hQ hY hR _hH _hT hN derivativeLeftRoute derivativeRightRoute
    comparisonRoute dyadicRoute realRoute namedRoute structuralSame _pkgP _pkgN
  have hDerivativeLeft : UnaryHistory derivativeLeft :=
    unary_cont_closed hC hD derivativeLeftRoute
  have hDerivativeRight : UnaryHistory derivativeRight :=
    unary_cont_closed hDerivativeLeft hD derivativeRightRoute
  have hComparison : UnaryHistory comparisonRead :=
    unary_cont_closed hD hL comparisonRoute
  have hDyadic : UnaryHistory dyadicRead :=
    unary_cont_closed hQ hY dyadicRoute
  have hReal : UnaryHistory realRead :=
    unary_cont_closed hDyadic hR realRoute
  have hNamed : UnaryHistory namedRead :=
    unary_cont_closed hReal hN namedRoute
  have sourceNamed : hsame namedRead namedRead ∧ UnaryHistory namedRead :=
    ⟨hsame_refl namedRead, hNamed⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row L ∨ hsame row Q ∨ hsame row Y ∨
              hsame row R ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeLeft ∧
              Cont derivativeLeft D derivativeRight ∧ Cont D L comparisonRead ∧
                Cont Q Y dyadicRead ∧ Cont dyadicRead R realRead ∧
                  Cont realRead N namedRead ∧ hsame H (append T P))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead sourceNamed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeLeftRoute, derivativeRightRoute, comparisonRoute,
          dyadicRoute, realRoute, namedRoute, structuralSame⟩
  }
  exact ⟨cert, hNamed⟩

theorem CalculusFiniteLimitSealDependencyRoute [AskSetup] [PackageSetup]
    {real limit continuous derivative integral readback transport replay provenance
      localName derivativeRead integralRead endpointRead finiteSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusRootDerivativeIntegralCarrier real limit continuous derivative integral readback
        transport replay provenance localName bundle pkg →
      Cont continuous derivative derivativeRead →
        Cont integral readback integralRead →
          Cont derivativeRead integralRead endpointRead →
            Cont endpointRead limit finiteSeal →
              Cont finiteSeal real publicRead →
                PkgSig bundle publicRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row derivativeRead ∨ hsame row integralRead ∨
                          hsame row endpointRead ∨ hsame row finiteSeal ∨
                            hsame row publicRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont endpointRead limit finiteSeal ∧
                          Cont finiteSeal real publicRead ∧ PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory finiteSeal ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier derivativeRoute integralRoute endpointRoute finiteRoute publicRoute publicPkg
  obtain ⟨realUnary, limitUnary, continuousUnary, derivativeUnary, integralUnary,
    readbackUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _realLimitRoute, _continuousDerivativeRoute, _derivativeTransportRoute,
    _transportReplayRoute, _provenancePkg⟩ := carrier
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed continuousUnary derivativeUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary endpointRoute
  have finiteSealUnary : UnaryHistory finiteSeal :=
    unary_cont_closed endpointReadUnary limitUnary finiteRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed finiteSealUnary realUnary publicRoute
  have publicSource :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row integralRead ∨ hsame row endpointRead ∨
              hsame row finiteSeal ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpointRead limit finiteSeal ∧
              Cont finiteSeal real publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead publicSource
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
      exact ⟨source.right, finiteRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, finiteSealUnary, publicReadUnary⟩

theorem CalculusFiniteLimitSealDependency [AskSetup] [PackageSetup]
    {derivativeRow integralRow regSeqRow realRow modulusRow windowRow readbackRow
      toleranceRow sealRow derivativeRead integralRead sharedRead endpointRead sealRead
      limitRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory derivativeRow →
      UnaryHistory integralRow →
        UnaryHistory regSeqRow →
          UnaryHistory realRow →
            UnaryHistory modulusRow →
              UnaryHistory windowRow →
                UnaryHistory toleranceRow →
                  Cont derivativeRow regSeqRow derivativeRead →
                    Cont integralRow regSeqRow integralRead →
                      Cont derivativeRead integralRead sharedRead →
                        Cont sharedRead realRow endpointRead →
                          Cont modulusRow windowRow readbackRow →
                            Cont readbackRow toleranceRow sealRead →
                              Cont endpointRead sealRead limitRead →
                                PkgSig bundle provenance pkg →
                                  PkgSig bundle localName pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row limitRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row derivativeRead ∨
                                            hsame row integralRead ∨
                                              hsame row endpointRead ∨
                                                hsame row sealRead ∨
                                                  hsame row limitRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont endpointRead sealRead limitRead ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle localName pkg)
                                        hsame ∧
                                      UnaryHistory endpointRead ∧ UnaryHistory sealRead ∧
                                        UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro derivativeUnary integralUnary regSeqUnary realUnary modulusUnary windowUnary
    toleranceUnary derivativeRoute integralRoute sharedRoute endpointRoute readbackRoute
    sealRoute limitRoute provenancePkg localNamePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary regSeqUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary regSeqUnary integralRoute
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_cont_closed derivativeReadUnary integralReadUnary sharedRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed sharedReadUnary realUnary endpointRoute
  have readbackRowUnary : UnaryHistory readbackRow :=
    unary_cont_closed modulusUnary windowUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackRowUnary toleranceUnary sealRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed endpointReadUnary sealReadUnary limitRoute
  have _sealRowSelf : hsame sealRow sealRow := hsame_refl sealRow
  have sourceAtLimit : hsame limitRead limitRead ∧ UnaryHistory limitRead :=
    ⟨hsame_refl limitRead, limitReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row limitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row derivativeRead ∨ hsame row integralRead ∨ hsame row endpointRead ∨
              hsame row sealRead ∨ hsame row limitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpointRead sealRead limitRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro limitRead sourceAtLimit
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
      exact ⟨source.right, limitRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, endpointReadUnary, sealReadUnary, limitReadUnary⟩

end BEDC.Derived.CalculusUp
