import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_radius_majorant_coverage [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N coefficientRead radiusMajorantRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      Cont A W coefficientRead ->
        Cont R S radiusMajorantRead ->
          Cont radiusMajorantRead E endpointRead ->
            PkgSig bundle endpointRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ∧
                      hsame row endpointRead)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row R ∨ hsame row W ∨ hsame row S ∨
                      hsame row M ∨ hsame row E ∨ hsame row endpointRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
                  hsame ∧
                UnaryHistory coefficientRead ∧ UnaryHistory radiusMajorantRead ∧
                  UnaryHistory endpointRead ∧ Cont A W coefficientRead ∧
                    Cont R S radiusMajorantRead ∧ Cont radiusMajorantRead E endpointRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute radiusMajorantRoute endpointRoute endpointPkg
  have carrierPacket : RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg :=
    carrier
  obtain ⟨AUnary, _ZUnary, _XUnary, RUnary, WUnary, SUnary, _MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed AUnary WUnary coefficientRoute
  have radiusMajorantUnary : UnaryHistory radiusMajorantRead :=
    unary_cont_closed RUnary SUnary radiusMajorantRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed radiusMajorantUnary EUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ∧
              hsame row endpointRead)
          (fun row : BHist =>
            hsame row A ∨ hsame row R ∨ hsame row W ∨ hsame row S ∨
              hsame row M ∨ hsame row E ∨ hsame row endpointRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead
        ⟨carrierPacket, hsame_refl endpointRead⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right)))))
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport endpointUnary (hsame_symm source.right), endpointPkg⟩
  }
  exact
    ⟨cert, coefficientUnary, radiusMajorantUnary, endpointUnary, coefficientRoute,
      radiusMajorantRoute, endpointRoute, pkgSig, endpointPkg⟩

end BEDC.Derived.RealPowerSeriesUp
