import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCarrier_endpoint_nonescape_triad [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N endpointRead radiusRead coeffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg →
      Cont S M radiusRead →
        Cont A W coeffRead →
          Cont M E endpointRead →
            PkgSig bundle endpointRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row coeffRead ∨ hsame row radiusRead ∨ hsame row endpointRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle endpointRead pkg ∧
                      Cont M E endpointRead)
                  hsame ∧
                UnaryHistory coeffRead ∧ UnaryHistory radiusRead ∧
                  UnaryHistory endpointRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier radiusRoute coeffRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, pkgSig⟩ := carrier
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed SUnary MUnary radiusRoute
  have coeffReadUnary : UnaryHistory coeffRead :=
    unary_cont_closed AUnary WUnary coeffRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed MUnary EUnary endpointRoute
  have sourceEndpoint :
      (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row) endpointRead := by
    exact ⟨hsame_refl endpointRead, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coeffRead ∨ hsame row radiusRead ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle endpointRead pkg ∧
              Cont M E endpointRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpointRead sourceEndpoint
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
      exact ⟨source.right, endpointPkg, endpointRoute⟩
  }
  exact ⟨cert, coeffReadUnary, radiusReadUnary, endpointUnary, pkgSig⟩

end BEDC.Derived.RealPowerSeriesUp
