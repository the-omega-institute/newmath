import BEDC.Derived.RegularCauchyModulusNormalizerUp.NormalizedRouteBridge

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerUp_StdBridge [AskSetup] [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont name route bridgeRead →
        PkgSig bundle bridgeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row x ∨ hsame row y ∨ hsame row muX ∨ hsame row muY ∨
                  hsame row meet ∨ hsame row window ∨ hsame row dyadic ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row transport ∨
                      hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row bridgeRead)
              (fun _row : BHist =>
                UnaryHistory bridgeRead ∧ Cont muX muY meet ∧ Cont meet window dyadic ∧
                  Cont dyadic readback sealRow ∧ Cont sealRow transport route ∧
                    Cont route provenance name ∧ Cont name route bridgeRead ∧
                      PkgSig bundle bridgeRead pkg)
              hsame ∧
            UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier nameRouteBridge bridgePkg
  rcases carrier with
    ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, _meetUnary, _windowUnary, _dyadicUnary,
      _readbackUnary, _sealUnary, _transportUnary, routeUnary, _provenanceUnary,
      nameUnary, sourceMeet, meetWindowDyadic, dyadicReadbackSeal, sealTransportRoute,
      routeProvenanceName, _meetPkg, _namePkg⟩
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed nameUnary routeUnary nameRouteBridge
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
                                  (Or.inr source.left))))))))))))
      ledger_sound := by
        intro _row _source
        exact
          ⟨bridgeUnary, sourceMeet, meetWindowDyadic, dyadicReadbackSeal,
            sealTransportRoute, routeProvenanceName, nameRouteBridge, bridgePkg⟩
    }
  · exact bridgeUnary

end BEDC.Derived.RegularCauchyModulusNormalizerUp
