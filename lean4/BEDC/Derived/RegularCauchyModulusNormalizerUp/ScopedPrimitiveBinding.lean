import BEDC.Derived.RegularCauchyModulusNormalizerUp

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyModulusNormalizerCarrier_scoped_primitive_binding [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg →
      Cont readback sealRow scopedRead →
        PkgSig bundle scopedRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic
                    readback sealRow transport route provenance name bundle pkg ∧
                  (hsame row meet ∨ hsame row window ∨ hsame row dyadic ∨
                    hsame row scopedRead ∨ hsame row name))
              (fun row : BHist =>
                Cont muX muY meet ∧ Cont meet window dyadic ∧
                  Cont dyadic readback sealRow ∧ Cont readback sealRow scopedRead ∧
                    (hsame row meet ∨ hsame row window ∨ hsame row dyadic ∨
                      hsame row scopedRead ∨ hsame row name))
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle name pkg ∧ PkgSig bundle scopedRead pkg)
              hsame ∧
            UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier readbackSealScoped scopedPkg
  have carrierWitness := carrier
  obtain ⟨_xUnary, _yUnary, _muXUnary, _muYUnary, meetUnary, windowUnary, dyadicUnary,
    readbackUnary, sealUnary, _transportUnary, _routeUnary, _provenanceUnary, nameUnary,
    sourceMeet, meetWindowDyadic, dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _meetPkg, namePkg⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed readbackUnary sealUnary readbackSealScoped
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                sealRow transport route provenance name bundle pkg ∧
              (hsame row meet ∨ hsame row window ∨ hsame row dyadic ∨
                hsame row scopedRead ∨ hsame row name))
          (fun row : BHist =>
            Cont muX muY meet ∧ Cont meet window dyadic ∧
              Cont dyadic readback sealRow ∧ Cont readback sealRow scopedRead ∧
                (hsame row meet ∨ hsame row window ∨ hsame row dyadic ∨
                  hsame row scopedRead ∨ hsame row name))
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle name pkg ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro meet ⟨carrierWitness, Or.inl (hsame_refl meet)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl rowMeet =>
            exact Or.inl (hsame_trans (hsame_symm same) rowMeet)
        | inr tail =>
            cases tail with
            | inl rowWindow =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) rowWindow))
            | inr tail =>
                cases tail with
                | inl rowDyadic =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm same) rowDyadic)))
                | inr tail =>
                    cases tail with
                    | inl rowScoped =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inl
                            (hsame_trans (hsame_symm same) rowScoped))))
                    | inr rowName =>
                        exact Or.inr
                          (Or.inr (Or.inr (Or.inr
                            (hsame_trans (hsame_symm same) rowName))))
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨sourceMeet, meetWindowDyadic, dyadicReadbackSeal, readbackSealScoped,
          source.right⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source.right with
        | inl rowMeet =>
            exact unary_transport meetUnary (hsame_symm rowMeet)
        | inr tail =>
            cases tail with
            | inl rowWindow =>
                exact unary_transport windowUnary (hsame_symm rowWindow)
            | inr tail =>
                cases tail with
                | inl rowDyadic =>
                    exact unary_transport dyadicUnary (hsame_symm rowDyadic)
                | inr tail =>
                    cases tail with
                    | inl rowScoped =>
                        exact unary_transport scopedUnary (hsame_symm rowScoped)
                    | inr rowName =>
                        exact unary_transport nameUnary (hsame_symm rowName)
      exact ⟨rowUnary, namePkg, scopedPkg⟩
  }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
