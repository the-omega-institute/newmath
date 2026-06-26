import BEDC.Derived.PseudometricUp.SeparatedQuotientHandoff

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_bridged_route [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      quotientRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont zeroRow transport quotientRead ->
        Cont quotientRead replay bridgeRead ->
          PkgSig bundle bridgeRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row point ∨ hsame row distance ∨ hsame row zeroRow ∨
                    hsame row quotientRead ∨ hsame row bridgeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle bridgeRead pkg)
                hsame ∧
              UnaryHistory quotientRead ∧ UnaryHistory bridgeRead ∧
                Cont stream readback dyadic ∧ Cont dyadic sealRow zeroRow := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier zeroTransportQuotient quotientReplayBridge bridgePkg
  obtain ⟨_pointUnary, _distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    streamReadbackDyadic, dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have quotientUnary : UnaryHistory quotientRead :=
    unary_cont_closed zeroUnary transportUnary zeroTransportQuotient
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed quotientUnary replayUnary quotientReplayBridge
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row distance ∨ hsame row zeroRow ∨
              hsame row quotientRead ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
      exact ⟨source.right, localNamePkg, bridgePkg⟩
  }
  exact ⟨cert, quotientUnary, bridgeUnary, streamReadbackDyadic, dyadicSealZero⟩

end BEDC.Derived.PseudometricUp
