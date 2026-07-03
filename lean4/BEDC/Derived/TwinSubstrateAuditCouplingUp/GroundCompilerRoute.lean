import BEDC.Derived.TwinSubstrateAuditCouplingUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TwinSubstrateAuditCouplingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TwinSubstrateAuditCouplingCarrier_groundcompiler_route [AskSetup] [PackageSetup]
    {M G R L C H T P N groundRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N G →
      TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N R →
        TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N C →
          UnaryHistory G →
            UnaryHistory R →
              UnaryHistory C →
                UnaryHistory H →
                  Cont G R groundRead →
                    Cont groundRead C replayRead →
                      PkgSig bundle replayRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N
                                  row ∨
                                hsame row groundRead ∨ hsame row replayRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont G R groundRead ∧
                                Cont groundRead C replayRead ∧
                                  PkgSig bundle replayRead pkg)
                            hsame ∧
                          UnaryHistory groundRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro _gSpec _rSpec _cSpec gUnary rUnary cUnary _hUnary groundRoute replayRoute replayPkg
  have groundUnary : UnaryHistory groundRead :=
    unary_cont_closed gUnary rUnary groundRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed groundUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            TwinSubstrateAuditCouplingObligationRowSpec M G R L C H T P N row ∨
              hsame row groundRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G R groundRead ∧ Cont groundRead C replayRead ∧
              PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨replayRead, hsame_refl replayRead, replayUnary⟩
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
      exact ⟨source.right, groundRoute, replayRoute, replayPkg⟩
  }
  exact ⟨cert, groundUnary, replayUnary⟩

end BEDC.Derived.TwinSubstrateAuditCouplingUp
