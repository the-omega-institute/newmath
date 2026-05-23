import BEDC.Derived.BetaReductionAuditTrailUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BetaReductionAuditTrailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BetaReductionAuditTrailNameCertObligations [AskSetup] [PackageSetup]
    {S V O D H C P N stageRead conversionRead obstructionRead dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory V ->
        UnaryHistory O ->
          UnaryHistory D ->
            UnaryHistory H ->
              Cont S V stageRead ->
                Cont stageRead O conversionRead ->
                  Cont conversionRead D obstructionRead ->
                    Cont obstructionRead H dischargeRead ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                          (fun row : BHist => hsame row dischargeRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            Cont S V stageRead ∧ Cont stageRead O conversionRead ∧
                              Cont conversionRead D obstructionRead ∧
                                Cont obstructionRead H row)
                          (fun row : BHist => hsame row dischargeRead ∧ PkgSig bundle N pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryS unaryV unaryO unaryD unaryH stageRoute conversionRoute obstructionRoute
    dischargeRoute namePkg
  have stageReadUnary : UnaryHistory stageRead :=
    unary_cont_closed unaryS unaryV stageRoute
  have conversionReadUnary : UnaryHistory conversionRead :=
    unary_cont_closed stageReadUnary unaryO conversionRoute
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed conversionReadUnary unaryD obstructionRoute
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed obstructionReadUnary unaryH dischargeRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro dischargeRead ⟨hsame_refl dischargeRead, dischargeReadUnary⟩
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
      exact ⟨stageRoute, conversionRoute, obstructionRoute,
        cont_result_hsame_transport dischargeRoute (hsame_symm source.left)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }

end BEDC.Derived.BetaReductionAuditTrailUp
