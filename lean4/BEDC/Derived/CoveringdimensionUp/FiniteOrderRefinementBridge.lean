import BEDC.Derived.CoveringdimensionUp.FiniteRefinementNameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteOrderRefinementBridge [AskSetup] [PackageSetup]
    {K E C R O L S M A G H T P N densityRead orderRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteRefinementCarrier K E C R O L S M A G H T P N bundle pkg →
      Cont E C densityRead →
        Cont densityRead O orderRead →
          Cont O L namedRead →
            PkgSig bundle orderRead pkg →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨
                        hsame row O ∨ hsame row L ∨ hsame row S ∨ hsame row P ∨
                          hsame row N ∨ hsame row densityRead ∨ hsame row orderRead ∨
                            hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont E C densityRead ∧
                        Cont densityRead O orderRead ∧ Cont O L namedRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle orderRead pkg ∧
                            PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory densityRead ∧ UnaryHistory orderRead ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionFiniteRefinementCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier densityRoute orderRoute namedRoute orderPkg namedPkg
  obtain ⟨_KUnary, EUnary, CUnary, _RUnary, OUnary, LUnary, _SUnary, _MUnary,
    _AUnary, _GUnary, _HUnary, _TUnary, _PUnary, _NUnary, _KELedger, _CROrder,
    _OLTReplay, _SMAWindow, _AGTransport, _HTProvenance, provenancePkg,
    _namePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed EUnary CUnary densityRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed densityUnary OUnary orderRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed OUnary LUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        right
        right
        right
        right
        right
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, densityRoute, orderRoute, namedRoute, provenancePkg, orderPkg,
            namedPkg⟩
    }
  · exact ⟨densityUnary, orderUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
