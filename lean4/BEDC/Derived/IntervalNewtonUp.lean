import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalNewtonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IntervalNewtonCarrier [AskSetup] [PackageSetup]
    (B F D N K V R H C P L : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory B ∧ UnaryHistory F ∧ UnaryHistory D ∧ UnaryHistory N ∧
    UnaryHistory K ∧ UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧ Cont V R L ∧
        PkgSig bundle L pkg

theorem IntervalNewtonKrawczykEnclosure [AskSetup] [PackageSetup]
    {B F D N K V R H C P L narrowed : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont N K narrowed ->
        PkgSig bundle narrowed pkg ->
          UnaryHistory B ∧ UnaryHistory N ∧ UnaryHistory K ∧ UnaryHistory V ∧
            UnaryHistory narrowed ∧ Cont N K narrowed ∧ PkgSig bundle L pkg ∧
              PkgSig bundle narrowed pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier narrowedRoute narrowedPkg
  obtain ⟨unaryB, _unaryF, _unaryD, unaryN, unaryK, unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _validatedLocal, localPkg⟩ := carrier
  have unaryNarrowed : UnaryHistory narrowed :=
    unary_cont_closed unaryN unaryK narrowedRoute
  exact
    ⟨unaryB, unaryN, unaryK, unaryV, unaryNarrowed, narrowedRoute, localPkg, narrowedPkg⟩

theorem IntervalNewtonNameCertObligations [AskSetup] [PackageSetup]
    {B F D N K V R H C P L containment validatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont N K containment ->
        Cont containment V validatedRead ->
          PkgSig bundle validatedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row B ∨ hsame row N ∨ hsame row K ∨ hsame row V ∨
                    hsame row validatedRead)
                (fun row : BHist =>
                  hsame row validatedRead ∧ PkgSig bundle validatedRead pkg)
                hsame ∧
              UnaryHistory B ∧ UnaryHistory N ∧ UnaryHistory K ∧
                UnaryHistory containment ∧ UnaryHistory validatedRead ∧
                  Cont N K containment ∧ Cont containment V validatedRead ∧
                    PkgSig bundle L pkg ∧ PkgSig bundle validatedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier containmentRoute validatedRoute validatedPkg
  obtain ⟨unaryB, _unaryF, _unaryD, unaryN, unaryK, unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _validatedLocal, localPkg⟩ := carrier
  have containmentUnary : UnaryHistory containment :=
    unary_cont_closed unaryN unaryK containmentRoute
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed containmentUnary unaryV validatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row N ∨ hsame row K ∨ hsame row V ∨
              hsame row validatedRead)
          (fun row : BHist =>
            hsame row validatedRead ∧ PkgSig bundle validatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro validatedRead ⟨hsame_refl validatedRead, validatedUnary⟩
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
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, validatedPkg⟩
  }
  exact
    ⟨cert, unaryB, unaryN, unaryK, containmentUnary, validatedUnary, containmentRoute,
      validatedRoute, localPkg, validatedPkg⟩

theorem IntervalNewtonCorrectionTransportScope [AskSetup] [PackageSetup]
    {B F D N K V R H C P L narrowed validatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont N K narrowed ->
        Cont narrowed V validatedRead ->
          PkgSig bundle narrowed pkg ->
            PkgSig bundle validatedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row B ∨ hsame row D ∨ hsame row N ∨ hsame row K ∨
                      hsame row V ∨ hsame row validatedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont N K narrowed ∧ Cont narrowed V validatedRead ∧
                      PkgSig bundle validatedRead pkg)
                  hsame ∧
                UnaryHistory narrowed ∧ UnaryHistory validatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier narrowedRoute validatedRoute _narrowedPkg validatedPkg
  obtain ⟨_unaryB, _unaryF, _unaryD, unaryN, unaryK, unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _validatedLocal, _localPkg⟩ := carrier
  have narrowedUnary : UnaryHistory narrowed :=
    unary_cont_closed unaryN unaryK narrowedRoute
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed narrowedUnary unaryV validatedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row validatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row D ∨ hsame row N ∨ hsame row K ∨
              hsame row V ∨ hsame row validatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N K narrowed ∧ Cont narrowed V validatedRead ∧
              PkgSig bundle validatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro validatedRead ⟨hsame_refl validatedRead, validatedUnary⟩
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
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, narrowedRoute, validatedRoute, validatedPkg⟩
  }
  exact ⟨cert, narrowedUnary, validatedUnary⟩

theorem IntervalNewtonContainmentObligation [AskSetup] [PackageSetup]
    {B F D N K V R H C P L containment : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg →
      Cont N K containment →
        UnaryHistory B ∧ UnaryHistory N ∧ UnaryHistory K ∧ UnaryHistory containment ∧
          Cont N K containment ∧ PkgSig bundle L pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier containmentRoute
  obtain ⟨unaryB, _unaryF, _unaryD, unaryN, unaryK, _unaryV, _unaryR, _unaryH,
    _unaryC, _unaryP, _unaryL, _localRoute, localPkg⟩ := carrier
  have unaryContainment : UnaryHistory containment :=
    unary_cont_closed unaryN unaryK containmentRoute
  exact ⟨unaryB, unaryN, unaryK, unaryContainment, containmentRoute, localPkg⟩

theorem IntervalNewtonKrawczykRadiusLock [AskSetup] [PackageSetup]
    {box fn deriv correction containment validated realSeal transport replay provenance localName
      radiusRead remainderRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalNewtonCarrier box fn deriv correction containment validated realSeal transport replay
        provenance localName bundle pkg →
      Cont correction deriv radiusRead →
        Cont radiusRead realSeal remainderRead →
          Cont containment validated consumerRead →
            PkgSig bundle consumerRead pkg →
              SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row correction ∨ hsame row deriv ∨ hsame row radiusRead ∨
                    hsame row remainderRead ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont correction deriv radiusRead ∧
                    Cont radiusRead realSeal remainderRead ∧
                      Cont containment validated consumerRead ∧
                        PkgSig bundle consumerRead pkg)
                hsame ∧ UnaryHistory radiusRead ∧ UnaryHistory remainderRead ∧
                  UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier correctionDerivRadius radiusRealSealRemainder containmentValidatedConsumer
    consumerPkg
  obtain ⟨_boxUnary, _fnUnary, derivUnary, correctionUnary, containmentUnary,
    validatedUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _validatedLocal, _localPkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed correctionUnary derivUnary correctionDerivRadius
  have remainderUnary : UnaryHistory remainderRead :=
    unary_cont_closed radiusUnary realSealUnary radiusRealSealRemainder
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed containmentUnary validatedUnary containmentValidatedConsumer
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row correction ∨ hsame row deriv ∨ hsame row radiusRead ∨
            hsame row remainderRead ∨ hsame row consumerRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont correction deriv radiusRead ∧
            Cont radiusRead realSeal remainderRead ∧ Cont containment validated consumerRead ∧
              PkgSig bundle consumerRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, correctionDerivRadius, radiusRealSealRemainder,
          containmentValidatedConsumer, consumerPkg⟩
  }
  exact ⟨cert, radiusUnary, remainderUnary, consumerUnary⟩

theorem IntervalNewtonValidatedConsumerBoundary [AskSetup] [PackageSetup]
    {box fn deriv correction containment validated realSeal transport replay provenance localName
      validatedRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalNewtonCarrier box fn deriv correction containment validated realSeal transport replay
        provenance localName bundle pkg →
      Cont containment validated validatedRead →
        Cont validatedRead realSeal boundaryRead →
          PkgSig bundle boundaryRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row containment ∨ hsame row validated ∨ hsame row validatedRead ∨
                  hsame row realSeal ∨ hsame row boundaryRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont containment validated validatedRead ∧
                  Cont validatedRead realSeal boundaryRead ∧ PkgSig bundle boundaryRead pkg)
              hsame ∧ UnaryHistory validatedRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier containmentValidatedRead validatedRealSealBoundary boundaryPkg
  obtain ⟨_boxUnary, _fnUnary, _derivUnary, _correctionUnary, containmentUnary,
    validatedUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _validatedLocal, _localPkg⟩ := carrier
  have validatedReadUnary : UnaryHistory validatedRead :=
    unary_cont_closed containmentUnary validatedUnary containmentValidatedRead
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed validatedReadUnary realSealUnary validatedRealSealBoundary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row containment ∨ hsame row validated ∨ hsame row validatedRead ∨
            hsame row realSeal ∨ hsame row boundaryRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont containment validated validatedRead ∧
            Cont validatedRead realSeal boundaryRead ∧ PkgSig bundle boundaryRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead
        ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, containmentValidatedRead, validatedRealSealBoundary, boundaryPkg⟩
  }
  exact ⟨cert, validatedReadUnary, boundaryUnary⟩

theorem IntervalNewtonValidatedHandoffObligation [AskSetup] [PackageSetup]
    {B F D N K V R H C P L validatedRead transportedRead replayRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntervalNewtonCarrier B F D N K V R H C P L bundle pkg ->
      Cont V R validatedRead ->
        Cont H C transportedRead ->
          Cont validatedRead transportedRead replayRead ->
            Cont replayRead L handoffRead ->
              PkgSig bundle handoffRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row V ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row L ∨ hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont V R validatedRead ∧
                        Cont H C transportedRead ∧
                          Cont validatedRead transportedRead replayRead ∧
                            Cont replayRead L handoffRead ∧
                              PkgSig bundle handoffRead pkg)
                    hsame ∧
                  UnaryHistory validatedRead ∧ UnaryHistory transportedRead ∧
                    UnaryHistory replayRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier validatedRoute transportedRoute replayRoute handoffRoute handoffPkg
  obtain ⟨_unaryB, _unaryF, _unaryD, _unaryN, _unaryK, unaryV, unaryR, unaryH,
    unaryC, _unaryP, unaryL, _validatedLocal, _localPkg⟩ := carrier
  have validatedUnary : UnaryHistory validatedRead :=
    unary_cont_closed unaryV unaryR validatedRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed unaryH unaryC transportedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed validatedUnary transportedUnary replayRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed replayUnary unaryL handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
              hsame row P ∨ hsame row L ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V R validatedRead ∧ Cont H C transportedRead ∧
              Cont validatedRead transportedRead replayRead ∧
                Cont replayRead L handoffRead ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead
        ⟨hsame_refl handoffRead, handoffUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, validatedRoute, transportedRoute, replayRoute, handoffRoute,
          handoffPkg⟩
  }
  exact ⟨cert, validatedUnary, transportedUnary, replayUnary, handoffUnary⟩

end BEDC.Derived.IntervalNewtonUp
