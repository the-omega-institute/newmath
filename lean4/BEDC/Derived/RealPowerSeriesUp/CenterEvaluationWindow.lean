import BEDC.Derived.RealPowerSeriesUp

namespace BEDC.Derived.RealPowerSeriesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealPowerSeriesCenterEvaluationWindow [AskSetup] [PackageSetup]
    {A Z X R W S M E H C P N constantWindow partialRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealPowerSeriesCarrier A Z X R W S M E H C P N bundle pkg ->
      hsame X Z ->
        Cont A W constantWindow ->
          Cont constantWindow S partialRead ->
            Cont partialRead M endpointRead ->
              PkgSig bundle endpointRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row Z ∨ hsame row X ∨ hsame row W ∨
                        hsame row S ∨ hsame row M ∨ hsame row endpointRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A W constantWindow ∧
                        Cont constantWindow S partialRead ∧
                          Cont partialRead M endpointRead ∧ PkgSig bundle endpointRead pkg)
                    hsame ∧
                  UnaryHistory constantWindow ∧ UnaryHistory partialRead ∧
                    UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier _centerArgumentSame constantRoute partialRoute endpointRoute endpointPkg
  obtain ⟨AUnary, _ZUnary, _XUnary, _RUnary, WUnary, SUnary, MUnary, _EUnary,
    _HUnary, _CUnary, _PUnary, _NUnary, _coefficientWindow, _radiusMajorant,
    _majorantEndpoint, _pkgSig⟩ := carrier
  have constantUnary : UnaryHistory constantWindow :=
    unary_cont_closed AUnary WUnary constantRoute
  have partialUnary : UnaryHistory partialRead :=
    unary_cont_closed constantUnary SUnary partialRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed partialUnary MUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row Z ∨ hsame row X ∨ hsame row W ∨
              hsame row S ∨ hsame row M ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A W constantWindow ∧
              Cont constantWindow S partialRead ∧ Cont partialRead M endpointRead ∧
                PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, constantRoute, partialRoute, endpointRoute, endpointPkg⟩
  }
  exact ⟨cert, constantUnary, partialUnary, endpointUnary⟩

end BEDC.Derived.RealPowerSeriesUp
