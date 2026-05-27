import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_radius_majorant_public_export [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coefficientRead radiusMajorantRead productRead
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coefficientRead ->
        Cont R S radiusMajorantRead ->
          Cont coefficientRead M productRead ->
            Cont productRead E endpointRead ->
              PkgSig bundle productRead pkg ->
                PkgSig bundle endpointRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row A ∨ hsame row R ∨ hsame row W ∨ hsame row S ∨
                          hsame row M ∨ hsame row E ∨ Cont productRead E endpointRead)
                      (fun row : BHist =>
                        PkgSig bundle productRead pkg ∧ PkgSig bundle endpointRead pkg ∧
                          hsame row endpointRead)
                      hsame ∧
                    UnaryHistory coefficientRead ∧ UnaryHistory radiusMajorantRead ∧
                      UnaryHistory productRead ∧ UnaryHistory endpointRead ∧
                        Cont A W coefficientRead ∧ Cont R S radiusMajorantRead ∧
                          Cont coefficientRead M productRead ∧
                            Cont productRead E endpointRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle productRead pkg ∧
                                PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute radiusRoute productRoute endpointRoute productPkg endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, carrierPkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed AUnary WUnary coefficientRoute
  have radiusMajorantUnary : UnaryHistory radiusMajorantRead :=
    unary_cont_closed RUnary SUnary radiusRoute
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed coefficientUnary MUnary productRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed productUnary EUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row M ∨
              hsame row E ∨ Cont productRead E endpointRead)
          (fun row : BHist =>
            PkgSig bundle productRead pkg ∧ PkgSig bundle endpointRead pkg ∧
              hsame row endpointRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead
        ⟨hsame_refl endpointRead, endpointUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr endpointRoute)))))
    ledger_sound := by
      intro _row source
      exact ⟨productPkg, endpointPkg, source.left⟩
  }
  exact
    ⟨cert, coefficientUnary, radiusMajorantUnary, productUnary, endpointUnary,
      coefficientRoute, radiusRoute, productRoute, endpointRoute, carrierPkg, productPkg,
      endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
