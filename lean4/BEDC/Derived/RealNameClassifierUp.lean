import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealNameClassifierUp [AskSetup] [PackageSetup]
    (source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  UnaryHistory source ∧ UnaryHistory stream ∧ UnaryHistory rat ∧ UnaryHistory dyadic ∧
    UnaryHistory tolerance ∧ UnaryHistory refinement ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont source stream replay ∧ Cont rat dyadic tolerance ∧
          Cont tolerance refinement sealRow ∧ hsame transport replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

namespace RealNameClassifierUp

theorem RealNameClassifierSource_tolerance_obligation [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont source tolerance refinement →
        PkgSig bundle provenance pkg →
          SemanticNameCert
            (fun row : BHist =>
              RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport
                replay provenance localName bundle pkg ∧ hsame row localName)
            (fun row : BHist =>
              RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport
                replay provenance localName bundle pkg ∧ hsame row localName)
            (fun row : BHist =>
              RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport
                replay provenance localName bundle pkg ∧ hsame row localName)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier _sourceToleranceRefinement _provenancePkg
  have carrierWitness :
      RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg :=
    carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrierWitness, hsame_refl localName⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceData
        exact ⟨sourceData.left, hsame_trans (hsame_symm same) sourceData.right⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact sourceData
    ledger_sound := by
      intro _row sourceData
      exact sourceData
  }

theorem RealNameClassifierCommonWindowSymmetry [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName swappedSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont dyadic rat tolerance →
        Cont tolerance refinement swappedSeal →
          PkgSig bundle swappedSeal pkg →
            SemanticNameCert
                (fun row : BHist => hsame row swappedSeal ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row stream ∨ hsame row rat ∨
                    hsame row dyadic ∨ hsame row tolerance ∨ hsame row swappedSeal)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont dyadic rat tolerance ∧
                    Cont tolerance refinement swappedSeal ∧ PkgSig bundle swappedSeal pkg)
                hsame ∧ UnaryHistory swappedSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro carrier dyadicRatRoute swappedSealRoute swappedPkg
  obtain ⟨_sourceUnary, _streamUnary, ratUnary, dyadicUnary, toleranceUnary,
    refinementUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _sourceStreamReplay, _ratDyadicTolerance, _toleranceRefinementSeal,
    _transportReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have toleranceUnaryFromSwappedWindow : UnaryHistory tolerance :=
    unary_cont_closed dyadicUnary ratUnary dyadicRatRoute
  have swappedUnary : UnaryHistory swappedSeal :=
    unary_cont_closed toleranceUnaryFromSwappedWindow refinementUnary swappedSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row swappedSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row stream ∨ hsame row rat ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row swappedSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic rat tolerance ∧
              Cont tolerance refinement swappedSeal ∧ PkgSig bundle swappedSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro swappedSeal ⟨hsame_refl swappedSeal, swappedUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceData.left))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, dyadicRatRoute, swappedSealRoute, swappedPkg⟩
  }
  exact ⟨cert, swappedUnary⟩

theorem RealNameClassifierSharedWindowEquivalence [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName swappedSeal composedSeal sharedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont dyadic rat tolerance →
        Cont tolerance refinement swappedSeal →
          Cont swappedSeal sealRow composedSeal →
            Cont composedSeal localName sharedRead →
              PkgSig bundle swappedSeal pkg →
                PkgSig bundle sharedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sharedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row stream ∨ hsame row rat ∨
                          hsame row dyadic ∨ hsame row tolerance ∨ hsame row swappedSeal ∨
                            hsame row composedSeal ∨ hsame row sharedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont dyadic rat tolerance ∧
                          Cont tolerance refinement swappedSeal ∧
                            Cont swappedSeal sealRow composedSeal ∧
                              Cont composedSeal localName sharedRead ∧
                                PkgSig bundle sharedRead pkg)
                      hsame ∧
                    UnaryHistory swappedSeal ∧
                      UnaryHistory composedSeal ∧ UnaryHistory sharedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame SemanticNameCert
  intro carrier dyadicRatRoute swappedSealRoute composedSealRoute sharedReadRoute _swappedPkg
    sharedPkg
  obtain ⟨_sourceUnary, _streamUnary, ratUnary, dyadicUnary, _toleranceUnary,
    refinementUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _sourceStreamReplay, _ratDyadicTolerance, _toleranceRefinementSeal,
    _transportReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have toleranceUnaryFromSharedWindow : UnaryHistory tolerance :=
    unary_cont_closed dyadicUnary ratUnary dyadicRatRoute
  have swappedUnary : UnaryHistory swappedSeal :=
    unary_cont_closed toleranceUnaryFromSharedWindow refinementUnary swappedSealRoute
  have composedUnary : UnaryHistory composedSeal :=
    unary_cont_closed swappedUnary sealUnary composedSealRoute
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed composedUnary localNameUnary sharedReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sharedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row stream ∨ hsame row rat ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row swappedSeal ∨ hsame row composedSeal ∨
                hsame row sharedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic rat tolerance ∧
              Cont tolerance refinement swappedSeal ∧ Cont swappedSeal sealRow composedSeal ∧
                Cont composedSeal localName sharedRead ∧ PkgSig bundle sharedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sharedRead ⟨hsame_refl sharedRead, sharedUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sourceData.left))))))
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, dyadicRatRoute, swappedSealRoute, composedSealRoute,
          sharedReadRoute, sharedPkg⟩
  }
  exact ⟨cert, swappedUnary, composedUnary, sharedUnary⟩

theorem RealNameClassifierWindowCoverage [AskSetup] [PackageSetup]
    {sourceA sourceB commonWindow dyadicA dyadicB toleranceA toleranceB classifierRead
      readbackA readbackB sealRead transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp sourceA commonWindow dyadicA dyadicB toleranceA readbackA sealRead
        transport replay provenance localName bundle pkg →
      Cont commonWindow dyadicA toleranceA →
        Cont commonWindow dyadicB toleranceB →
          Cont toleranceA toleranceB classifierRead →
            Cont classifierRead readbackA readbackB →
              Cont readbackB sealRead localName →
                PkgSig bundle localName pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row commonWindow ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
                          hsame row toleranceA ∨ hsame row toleranceB ∨
                            hsame row classifierRead ∨ hsame row localName)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont commonWindow dyadicA toleranceA ∧
                          Cont commonWindow dyadicB toleranceB ∧
                            Cont toleranceA toleranceB classifierRead ∧
                              Cont classifierRead readbackA readbackB ∧
                                Cont readbackB sealRead localName ∧
                                  PkgSig bundle localName pkg)
                      hsame ∧
                    UnaryHistory toleranceA ∧ UnaryHistory toleranceB ∧
                      UnaryHistory classifierRead ∧ UnaryHistory readbackB ∧
                        UnaryHistory localName := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier toleranceARoute toleranceBRoute classifierRoute readbackRoute sealRoute localPkg
  have _sourceBReflexive : hsame sourceB sourceB := hsame_refl sourceB
  obtain ⟨_sourceUnary, commonWindowUnary, dyadicAUnary, dyadicBUnary, _toleranceAUnary,
    readbackAUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _sourceWindowReplay, _dyadicToleranceRoute, _toleranceReadbackSeal,
    _transportReplay, _provenancePkg, _carrierLocalPkg⟩ := carrier
  have toleranceAUnaryFromWindow : UnaryHistory toleranceA :=
    unary_cont_closed commonWindowUnary dyadicAUnary toleranceARoute
  have toleranceBUnary : UnaryHistory toleranceB :=
    unary_cont_closed commonWindowUnary dyadicBUnary toleranceBRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed toleranceAUnaryFromWindow toleranceBUnary classifierRoute
  have readbackBUnary : UnaryHistory readbackB :=
    unary_cont_closed classifierUnary readbackAUnary readbackRoute
  have localNameUnary : UnaryHistory localName :=
    unary_cont_closed readbackBUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row commonWindow ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
              hsame row toleranceA ∨ hsame row toleranceB ∨ hsame row classifierRead ∨
                hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont commonWindow dyadicA toleranceA ∧
              Cont commonWindow dyadicB toleranceB ∧
                Cont toleranceA toleranceB classifierRead ∧
                  Cont classifierRead readbackA readbackB ∧
                    Cont readbackB sealRead localName ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName ⟨hsame_refl localName, localNameUnary⟩
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
        ⟨source.right, toleranceARoute, toleranceBRoute, classifierRoute, readbackRoute,
          sealRoute, localPkg⟩
  }
  exact
    ⟨cert, toleranceAUnaryFromWindow, toleranceBUnary, classifierUnary, readbackBUnary,
      localNameUnary⟩

theorem RealNameClassifierCauchyCompletionHandoff [AskSetup] [PackageSetup]
    {sourceA sourceB commonWindow dyadicA dyadicB toleranceA toleranceB classifierRead
      readbackA readbackB sealRead transport replay provenance localName completionSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp sourceA commonWindow dyadicA dyadicB toleranceA readbackA sealRead
        transport replay provenance localName bundle pkg →
      Cont commonWindow dyadicA toleranceA →
        Cont commonWindow dyadicB toleranceB →
          Cont toleranceA toleranceB classifierRead →
            Cont classifierRead readbackA readbackB →
              Cont readbackB sealRead localName →
                Cont localName sealRead completionSeal →
                  PkgSig bundle completionSeal pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row completionSeal ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row commonWindow ∨ hsame row dyadicA ∨
                            hsame row dyadicB ∨ hsame row toleranceA ∨
                              hsame row toleranceB ∨ hsame row classifierRead ∨
                                hsame row readbackB ∨ hsame row localName ∨
                                  hsame row completionSeal)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont commonWindow dyadicA toleranceA ∧
                            Cont commonWindow dyadicB toleranceB ∧
                              Cont toleranceA toleranceB classifierRead ∧
                                Cont classifierRead readbackA readbackB ∧
                                  Cont readbackB sealRead localName ∧
                                    Cont localName sealRead completionSeal ∧
                                      PkgSig bundle completionSeal pkg)
                        hsame ∧ UnaryHistory toleranceA ∧ UnaryHistory toleranceB ∧
                      UnaryHistory classifierRead ∧ UnaryHistory readbackB ∧
                        UnaryHistory localName ∧ UnaryHistory completionSeal := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier toleranceARoute toleranceBRoute classifierRoute readbackRoute sealRoute
    completionRoute completionPkg
  have _sourceBReflexive : hsame sourceB sourceB := hsame_refl sourceB
  obtain ⟨_sourceUnary, commonWindowUnary, dyadicAUnary, dyadicBUnary, _toleranceAUnary,
    readbackAUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _sourceWindowReplay, _dyadicToleranceRoute, _toleranceReadbackSeal,
    _transportReplay, _provenancePkg, _carrierLocalPkg⟩ := carrier
  have toleranceAUnaryFromWindow : UnaryHistory toleranceA :=
    unary_cont_closed commonWindowUnary dyadicAUnary toleranceARoute
  have toleranceBUnary : UnaryHistory toleranceB :=
    unary_cont_closed commonWindowUnary dyadicBUnary toleranceBRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed toleranceAUnaryFromWindow toleranceBUnary classifierRoute
  have readbackBUnary : UnaryHistory readbackB :=
    unary_cont_closed classifierUnary readbackAUnary readbackRoute
  have localNameUnary : UnaryHistory localName :=
    unary_cont_closed readbackBUnary sealUnary sealRoute
  have completionUnary : UnaryHistory completionSeal :=
    unary_cont_closed localNameUnary sealUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row commonWindow ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
              hsame row toleranceA ∨ hsame row toleranceB ∨ hsame row classifierRead ∨
                hsame row readbackB ∨ hsame row localName ∨ hsame row completionSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont commonWindow dyadicA toleranceA ∧
              Cont commonWindow dyadicB toleranceB ∧
                Cont toleranceA toleranceB classifierRead ∧
                  Cont classifierRead readbackA readbackB ∧
                    Cont readbackB sealRead localName ∧
                      Cont localName sealRead completionSeal ∧
                        PkgSig bundle completionSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionSeal ⟨hsame_refl completionSeal, completionUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, toleranceARoute, toleranceBRoute, classifierRoute, readbackRoute,
          sealRoute, completionRoute, completionPkg⟩
  }
  exact
    ⟨cert, toleranceAUnaryFromWindow, toleranceBUnary, classifierUnary, readbackBUnary,
      localNameUnary, completionUnary⟩

end RealNameClassifierUp
end BEDC.Derived
