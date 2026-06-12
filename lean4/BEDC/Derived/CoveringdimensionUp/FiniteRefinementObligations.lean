import BEDC.Derived.CoveringdimensionUp.FiniteRefinementNameCert
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteRefinementObligations [AskSetup] [PackageSetup]
    {K E C R O L M S Q A H T P N completionRead densityRead compareRead realSealRead
      orderExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteRefinementCarrier K E C R O L M S Q A H T P N bundle pkg →
      Cont O L completionRead →
        Cont M S densityRead →
          Cont Q A compareRead →
            Cont completionRead densityRead realSealRead →
              Cont realSealRead compareRead orderExport →
                PkgSig bundle orderExport pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row orderExport ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row C ∨ hsame row R ∨ hsame row O ∨
                          hsame row L ∨ hsame row M ∨ hsame row S ∨ hsame row Q ∨
                            hsame row A ∨ hsame row orderExport)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle orderExport pkg)
                      hsame ∧ UnaryHistory completionRead ∧ UnaryHistory densityRead ∧
                    UnaryHistory compareRead ∧ UnaryHistory realSealRead ∧
                      UnaryHistory orderExport := by
  -- BEDC touchpoint anchor: CoveringDimensionFiniteRefinementCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute densityRoute compareRoute realSealRoute orderRoute orderPkg
  obtain ⟨KUnary, _EUnary, CUnary, RUnary, OUnary, LUnary, MUnary, SUnary, QUnary,
    AUnary, _HUnary, _TUnary, _PUnary, _NUnary, _KELedger, _CROrder, _OLTReplay,
    _SMAWindow, _AGTransport, _HTProvenance, _provenancePkg, _namePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed OUnary LUnary completionRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed MUnary SUnary densityRoute
  have compareUnary : UnaryHistory compareRead :=
    unary_cont_closed QUnary AUnary compareRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed completionUnary densityUnary realSealRoute
  have orderUnary : UnaryHistory orderExport :=
    unary_cont_closed realSealUnary compareUnary orderRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row orderExport ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row C ∨ hsame row R ∨ hsame row O ∨ hsame row L ∨
              hsame row M ∨ hsame row S ∨ hsame row Q ∨ hsame row A ∨
                hsame row orderExport)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle orderExport pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro orderExport ⟨hsame_refl orderExport, orderUnary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, orderPkg⟩
  }
  exact ⟨cert, completionUnary, densityUnary, compareUnary, realSealUnary, orderUnary⟩

end BEDC.Derived.CoveringdimensionUp
