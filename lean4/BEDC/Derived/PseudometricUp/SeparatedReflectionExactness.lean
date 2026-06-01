import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_zero_distance_separated_reflection_exactness
    [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      zeroBoundaryRead reflectedBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport
        replay localName bundle pkg →
      Cont zeroRow transport zeroBoundaryRead →
        Cont zeroBoundaryRead replay reflectedBoundary →
          PkgSig bundle reflectedBoundary pkg →
            SemanticNameCert
                (fun row : BHist => hsame row reflectedBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row zeroRow ∨ hsame row zeroBoundaryRead ∨
                    hsame row reflectedBoundary)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont zeroRow transport zeroBoundaryRead ∧
                    Cont zeroBoundaryRead replay reflectedBoundary ∧ hsame localName zeroRow ∧
                      PkgSig bundle reflectedBoundary pkg)
                hsame ∧
              UnaryHistory zeroBoundaryRead ∧ UnaryHistory reflectedBoundary ∧
                Cont stream readback dyadic ∧ Cont dyadic sealRow zeroRow ∧
                  hsame localName zeroRow ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle reflectedBoundary pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier zeroTransportBoundary boundaryReplayReflected reflectedPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, localNameZero, localNamePkg⟩ := carrier
  have zeroBoundaryUnary : UnaryHistory zeroBoundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroTransportBoundary
  have reflectedUnary : UnaryHistory reflectedBoundary :=
    unary_cont_closed zeroBoundaryUnary replayUnary boundaryReplayReflected
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row reflectedBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroRow ∨ hsame row zeroBoundaryRead ∨ hsame row reflectedBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont zeroRow transport zeroBoundaryRead ∧
              Cont zeroBoundaryRead replay reflectedBoundary ∧ hsame localName zeroRow ∧
                PkgSig bundle reflectedBoundary pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro reflectedBoundary ⟨hsame_refl reflectedBoundary, reflectedUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, zeroTransportBoundary, boundaryReplayReflected, localNameZero,
          reflectedPkg⟩
  }
  exact
    ⟨cert, zeroBoundaryUnary, reflectedUnary, streamReadbackDyadic, dyadicSealZero,
      localNameZero, localNamePkg, reflectedPkg⟩

theorem PseudometricZeroDistanceSeparatedReflectionExactness [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      zeroBoundaryRead separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont zeroRow transport zeroBoundaryRead ->
        Cont zeroBoundaryRead replay separatedRead ->
          PkgSig bundle separatedRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row zeroRow ∨ hsame row zeroBoundaryRead ∨
                    hsame row separatedRead ∨ hsame row transport ∨ hsame row replay ∨
                      hsame row localName)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle separatedRead pkg)
                hsame ∧
              UnaryHistory zeroBoundaryRead ∧ UnaryHistory separatedRead := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier zeroTransportBoundary boundaryReplaySeparated separatedPkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    _streamReadbackDyadic, _dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have zeroBoundaryUnary : UnaryHistory zeroBoundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroTransportBoundary
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed zeroBoundaryUnary replayUnary boundaryReplaySeparated
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroRow ∨ hsame row zeroBoundaryRead ∨ hsame row separatedRead ∨
              hsame row transport ∨ hsame row replay ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle separatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro separatedRead ⟨hsame_refl separatedRead, separatedUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localNamePkg, separatedPkg⟩
  }
  exact ⟨cert, zeroBoundaryUnary, separatedUnary⟩

end BEDC.Derived.PseudometricUp
