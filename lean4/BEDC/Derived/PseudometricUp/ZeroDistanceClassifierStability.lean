import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_zero_distance_classifier_stability [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      zeroRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg →
      Cont zeroRow transport zeroRead →
        Cont zeroRead replay stableRead →
          PkgSig bundle stableRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row zeroRow ∨ hsame row zeroRead ∨ hsame row stableRead ∨
                    Cont zeroRead replay stableRead)
                (fun row : BHist => PkgSig bundle stableRead pkg ∧ hsame row stableRead)
                hsame ∧
              UnaryHistory zeroRead ∧ UnaryHistory stableRead := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier zeroTransportRead readReplayStable stablePkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, _streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    _streamReadbackDyadic, _dyadicSealZero, _localNameZero, _localNamePkg⟩ := carrier
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed zeroUnary transportUnary zeroTransportRead
  have stableReadUnary : UnaryHistory stableRead :=
    unary_cont_closed zeroReadUnary replayUnary readReplayStable
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroRow ∨ hsame row zeroRead ∨ hsame row stableRead ∨
              Cont zeroRead replay stableRead)
          (fun row : BHist => PkgSig bundle stableRead pkg ∧ hsame row stableRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro stableRead ⟨hsame_refl stableRead, stableReadUnary⟩
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
      exact ⟨stablePkg, source.left⟩
  }
  exact ⟨cert, zeroReadUnary, stableReadUnary⟩

end BEDC.Derived.PseudometricUp
