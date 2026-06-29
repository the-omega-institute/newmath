import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationProvenanceNamingObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont Q N route →
        PkgSig bundle route pkg →
          SemanticNameCert
            (fun row : BHist => hsame row route ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
            (fun row : BHist =>
              Cont Q N row ∧ SheafificationCarrier C T J P L G S H R Q N bundle pkg)
            (fun row : BHist => PkgSig bundle row pkg ∧ Cont Q N route)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory
  intro carrier provenanceRoute routePkg
  have acceptedCarrier :
      SheafificationCarrier C T J P L G S H R Q N bundle pkg :=
    carrier
  obtain ⟨_cUnary, _tUnary, _jUnary, _pUnary, _lUnary, _gUnary, _sUnary, _hUnary,
    _rUnary, qUnary, nUnary, _qPkg, _nPkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed qUnary nUnary provenanceRoute
  refine
    { core :=
        { carrier_inhabited := ⟨route, hsame_refl route, routeUnary, routePkg⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    cases sameRows
    exact sourceRow
  · intro _row sourceRow
    exact
      ⟨cont_result_hsame_transport provenanceRoute (hsame_symm sourceRow.left),
        acceptedCarrier⟩
  · intro _row sourceRow
    exact ⟨sourceRow.right.right, provenanceRoute⟩

end BEDC.Derived.SheafificationUp
